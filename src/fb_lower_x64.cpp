// Fast Backend — x86-64 instruction lowering

// ───────────────────────────────────────────────────────────────────────
// Code emission primitives
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_low_emit_byte(fbLowCtx *ctx, u8 byte) {
	if (ctx->code_count >= ctx->code_cap) {
		u32 new_cap = ctx->code_cap * 2;
		if (new_cap < 256) new_cap = 256;
		ctx->code = gb_resize_array(heap_allocator(), ctx->code, ctx->code_cap, new_cap);
		ctx->code_cap = new_cap;
	}
	ctx->code[ctx->code_count++] = byte;
}

gb_internal void fb_low_emit_bytes(fbLowCtx *ctx, u8 const *bytes, u32 count) {
	for (u32 i = 0; i < count; i++) {
		fb_low_emit_byte(ctx, bytes[i]);
	}
}

// ───────────────────────────────────────────────────────────────────────
// x86-64 encoding helpers
// ───────────────────────────────────────────────────────────────────────

// Caller-saved GP registers available for allocation (excludes RSP, RBP)
gb_global fbX64Reg const fb_x64_gp_alloc_order[] = {
	FB_RAX, FB_RCX, FB_RDX, FB_RSI, FB_RDI,
	FB_R8, FB_R9, FB_R10, FB_R11,
};
gb_global u32 const FB_X64_GP_ALLOC_COUNT = gb_count_of(fb_x64_gp_alloc_order);

// REX prefix: 0100WRXB
// W=1 for 64-bit operand size, R=high bit of reg, X=high bit of index, B=high bit of rm/base
gb_internal void fb_x64_rex(fbLowCtx *ctx, bool w, u8 reg, u8 index, u8 rm) {
	u8 byte = 0x40;
	if (w)          byte |= 0x08;
	if (reg & 0x08) byte |= 0x04;  // REX.R
	if (index & 0x08) byte |= 0x02;  // REX.X
	if (rm & 0x08) byte |= 0x01;  // REX.B
	fb_low_emit_byte(ctx, byte);
}

// Emit REX only if needed (any register >= R8, or W bit needed)
gb_internal void fb_x64_rex_if_needed(fbLowCtx *ctx, bool w, u8 reg, u8 index, u8 rm) {
	if (w || (reg & 0x08) || (index & 0x08) || (rm & 0x08)) {
		fb_x64_rex(ctx, w, reg, index, rm);
	}
}

// ModRM byte: mod(2) | reg(3) | rm(3)
gb_internal void fb_x64_modrm(fbLowCtx *ctx, u8 mod, u8 reg, u8 rm) {
	fb_low_emit_byte(ctx, cast(u8)((mod << 6) | ((reg & 7) << 3) | (rm & 7)));
}

// SIB byte: scale(2) | index(3) | base(3)
gb_internal void fb_x64_sib(fbLowCtx *ctx, u8 scale, u8 index, u8 base) {
	fb_low_emit_byte(ctx, cast(u8)((scale << 6) | ((index & 7) << 3) | (base & 7)));
}

gb_internal void fb_x64_imm8(fbLowCtx *ctx, i8 val) {
	fb_low_emit_byte(ctx, cast(u8)val);
}

gb_internal void fb_x64_imm32(fbLowCtx *ctx, i32 val) {
	fb_low_emit_byte(ctx, cast(u8)(val & 0xFF));
	fb_low_emit_byte(ctx, cast(u8)((val >> 8) & 0xFF));
	fb_low_emit_byte(ctx, cast(u8)((val >> 16) & 0xFF));
	fb_low_emit_byte(ctx, cast(u8)((val >> 24) & 0xFF));
}

gb_internal void fb_x64_imm64(fbLowCtx *ctx, i64 val) {
	for (int i = 0; i < 8; i++) {
		fb_low_emit_byte(ctx, cast(u8)((val >> (i * 8)) & 0xFF));
	}
}

// Encode [rbp + disp32] addressing (mod=10, rm=5)
gb_internal void fb_x64_modrm_rbp_disp32(fbLowCtx *ctx, u8 reg, i32 disp) {
	fb_x64_modrm(ctx, 0x02, reg, FB_RBP);
	fb_x64_imm32(ctx, disp);
}

// Encode [reg] indirect addressing with special-case handling for RBP and RSP.
// RBP in mod=00 rm=5 means [RIP+disp32], so we use mod=01 with disp8=0.
// RSP in rm=4 means "SIB follows", so we emit SIB(0, RSP, RSP).
gb_internal void fb_x64_modrm_indirect(fbLowCtx *ctx, u8 reg, u8 base) {
	if ((base & 7) == FB_RBP) {
		// [RBP] -> mod=01, rm=5, disp8=0
		fb_x64_modrm(ctx, 0x01, reg, base);
		fb_x64_imm8(ctx, 0);
	} else if ((base & 7) == FB_RSP) {
		// [RSP] -> mod=00, rm=4, SIB(0, 4, 4)
		fb_x64_modrm(ctx, 0x00, reg, base);
		fb_x64_sib(ctx, 0, FB_RSP, FB_RSP);
	} else {
		fb_x64_modrm(ctx, 0x00, reg, base);
	}
}

// MOV reg, reg (64-bit)
gb_internal void fb_x64_mov_rr(fbLowCtx *ctx, fbX64Reg dst, fbX64Reg src) {
	fb_x64_rex(ctx, true, src, 0, dst);
	fb_low_emit_byte(ctx, 0x89);
	fb_x64_modrm(ctx, 0x03, src, dst);
}

// MOV reg, imm32 (sign-extended to 64-bit): REX.W C7 /0 imm32
gb_internal void fb_x64_mov_ri32(fbLowCtx *ctx, fbX64Reg dst, i32 val) {
	fb_x64_rex(ctx, true, 0, 0, dst);
	fb_low_emit_byte(ctx, 0xC7);
	fb_x64_modrm(ctx, 0x03, 0, dst);
	fb_x64_imm32(ctx, val);
}

// MOV reg, imm64 (movabs): REX.W B8+rd imm64
gb_internal void fb_x64_mov_ri64(fbLowCtx *ctx, fbX64Reg dst, i64 val) {
	fb_x64_rex(ctx, true, 0, 0, dst);
	fb_low_emit_byte(ctx, cast(u8)(0xB8 + (dst & 7)));
	fb_x64_imm64(ctx, val);
}

// ───────────────────────────────────────────────────────────────────────
// Register allocator
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_spill_reg(fbLowCtx *ctx, fbX64Reg reg);

gb_internal void fb_x64_reset_regs(fbLowCtx *ctx) {
	// Spill dirty registers before clearing — ensures value_loc is
	// consistent with reality at block boundaries.
	for (u32 i = 0; i < FB_X64_GP_ALLOC_COUNT; i++) {
		fbX64Reg r = fb_x64_gp_alloc_order[i];
		if (ctx->gp[r].vreg != FB_NOREG && ctx->gp[r].dirty) {
			fb_x64_spill_reg(ctx, r);
		}
	}
	for (int i = 0; i < 16; i++) {
		ctx->gp[i].vreg     = FB_NOREG;
		ctx->gp[i].last_use = 0;
		ctx->gp[i].dirty    = false;
	}
}

gb_internal void fb_x64_init_value_loc(fbLowCtx *ctx) {
	u32 count = ctx->proc->next_value;
	ctx->value_loc_count = count;
	if (count > 0) {
		ctx->value_loc = gb_alloc_array(heap_allocator(), i32, count);
		for (u32 i = 0; i < count; i++) {
			ctx->value_loc[i] = FB_LOC_NONE;
		}
	}
}

// Compute spill offset for value vreg: [rbp - slot_area - (vreg+1)*8]
gb_internal i32 fb_x64_spill_offset(fbLowCtx *ctx, u32 vreg) {
	return -cast(i32)ctx->frame.slot_area_size - cast(i32)((vreg + 1) * 8);
}

// Find the least-recently-used register among the allocatable set, skipping masked registers
gb_internal fbX64Reg fb_x64_find_lru(fbLowCtx *ctx, u16 exclude_mask) {
	u32 best_use = UINT32_MAX;
	fbX64Reg best = FB_X64_REG_NONE;
	for (u32 i = 0; i < FB_X64_GP_ALLOC_COUNT; i++) {
		fbX64Reg r = fb_x64_gp_alloc_order[i];
		if ((exclude_mask >> r) & 1) continue;
		if (ctx->gp[r].vreg == FB_NOREG) continue;
		if (ctx->gp[r].last_use < best_use) {
			best_use = ctx->gp[r].last_use;
			best = r;
		}
	}
	GB_ASSERT(best != FB_X64_REG_NONE);
	return best;
}

// Spill a register to its spill slot: mov [rbp+offset], reg
gb_internal void fb_x64_spill_reg(fbLowCtx *ctx, fbX64Reg reg) {
	u32 vreg = ctx->gp[reg].vreg;
	if (vreg == FB_NOREG) return;
	i32 offset = fb_x64_spill_offset(ctx, vreg);
	if (ctx->gp[reg].dirty) {
		// mov [rbp+disp32], reg (64-bit)
		fb_x64_rex(ctx, true, reg, 0, FB_RBP);
		fb_low_emit_byte(ctx, 0x89);
		fb_x64_modrm_rbp_disp32(ctx, reg, offset);
		ctx->gp[reg].dirty = false;
	}
	ctx->value_loc[vreg] = offset;
	ctx->gp[reg].vreg = FB_NOREG;
}

// Allocate a GP register for vreg. Finds free or evicts LRU.
// exclude_mask: bitmask of registers to not allocate (one bit per hardware register)
gb_internal fbX64Reg fb_x64_alloc_gp(fbLowCtx *ctx, u32 vreg, u16 exclude_mask) {
	// First: try to find a free register
	for (u32 i = 0; i < FB_X64_GP_ALLOC_COUNT; i++) {
		fbX64Reg r = fb_x64_gp_alloc_order[i];
		if ((exclude_mask >> r) & 1) continue;
		if (ctx->gp[r].vreg == FB_NOREG) {
			ctx->gp[r].vreg     = vreg;
			ctx->gp[r].last_use = ctx->current_inst_idx;
			ctx->gp[r].dirty    = true;
			if (vreg != FB_NOREG) {
				ctx->value_loc[vreg] = cast(i32)r;
			}
			return r;
		}
	}
	// Evict LRU (find_lru already respects the mask)
	fbX64Reg victim = fb_x64_find_lru(ctx, exclude_mask);
	fb_x64_spill_reg(ctx, victim);
	ctx->gp[victim].vreg     = vreg;
	ctx->gp[victim].last_use = ctx->current_inst_idx;
	ctx->gp[victim].dirty    = true;
	if (vreg != FB_NOREG) {
		ctx->value_loc[vreg] = cast(i32)victim;
	}
	return victim;
}

// Resolve a value into a GP register. If already in a register, return it.
// If spilled, reload it. If not yet materialized, allocate fresh.
// exclude_mask: bitmask of registers to avoid when allocating (ignored if value already in a register)
gb_internal fbX64Reg fb_x64_resolve_gp(fbLowCtx *ctx, u32 vreg, u16 exclude_mask) {
	GB_ASSERT(vreg < ctx->value_loc_count);
	i32 loc = ctx->value_loc[vreg];

	// Already in a register?
	if (loc >= 0 && loc < 16) {
		fbX64Reg r = cast(fbX64Reg)loc;
		GB_ASSERT(ctx->gp[r].vreg == vreg);
		ctx->gp[r].last_use = ctx->current_inst_idx;
		return r;
	}

	// Spilled or not yet materialized — allocate and reload
	fbX64Reg r = fb_x64_alloc_gp(ctx, vreg, exclude_mask);
	if (loc != FB_LOC_NONE) {
		// Reload from spill slot: mov reg, [rbp+disp32]
		fb_x64_rex(ctx, true, r, 0, FB_RBP);
		fb_low_emit_byte(ctx, 0x8B);
		fb_x64_modrm_rbp_disp32(ctx, r, loc);
		ctx->gp[r].dirty = false; // just loaded, matches memory
	}
	return r;
}

// Move an IR value into a specific physical register.
// Handles spilling the current occupant, moving from another register, or reloading from stack.
gb_internal void fb_x64_move_value_to_reg(fbLowCtx *ctx, u32 vreg, fbX64Reg target) {
	GB_ASSERT(vreg < ctx->value_loc_count);
	i32 loc = ctx->value_loc[vreg];

	// Already in the target register — nothing to do
	if (loc == cast(i32)target) {
		GB_ASSERT(ctx->gp[target].vreg == vreg);
		ctx->gp[target].last_use = ctx->current_inst_idx;
		return;
	}

	// Spill target if occupied by a different value
	if (ctx->gp[target].vreg != FB_NOREG && ctx->gp[target].vreg != vreg) {
		fb_x64_spill_reg(ctx, target);
	}

	if (loc >= 0 && loc < 16) {
		// Value is in another register — mov target, src
		fbX64Reg src = cast(fbX64Reg)loc;
		fb_x64_mov_rr(ctx, target, src);
		ctx->gp[src].vreg = FB_NOREG;
	} else if (loc != FB_LOC_NONE) {
		// Value is on the stack — reload
		fb_x64_rex(ctx, true, target, 0, FB_RBP);
		fb_low_emit_byte(ctx, 0x8B);
		fb_x64_modrm_rbp_disp32(ctx, target, loc);
	}

	ctx->gp[target].vreg     = vreg;
	ctx->gp[target].last_use = ctx->current_inst_idx;
	ctx->gp[target].dirty    = (loc >= 0 && loc < 16); // dirty if moved from reg, clean if reloaded
	ctx->value_loc[vreg]     = cast(i32)target;
}

// ───────────────────────────────────────────────────────────────────────
// Stack frame layout
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_compute_frame(fbLowCtx *ctx) {
	fbProc *p = ctx->proc;

	// Sort slots by alignment descending via index array (preserves slot indices for ALLOCA)
	u32 *order = nullptr;
	if (p->slot_count > 0) {
		order = gb_alloc_array(heap_allocator(), u32, p->slot_count);
		for (u32 i = 0; i < p->slot_count; i++) order[i] = i;
		// Insertion sort on order[], comparing alignment descending
		for (u32 i = 1; i < p->slot_count; i++) {
			u32 tmp = order[i];
			u32 j = i;
			while (j > 0 && p->slots[order[j-1]].align < p->slots[tmp].align) {
				order[j] = order[j-1];
				j--;
			}
			order[j] = tmp;
		}
	}

	// Assign negative offsets from RBP in sorted order
	i32 offset = 0;
	for (u32 i = 0; i < p->slot_count; i++) {
		fbStackSlot *s = &p->slots[order[i]];
		i32 align = cast(i32)s->align;
		if (align < 1) align = 1;
		offset += cast(i32)s->size;
		// Round up to alignment
		offset = (offset + align - 1) & ~(align - 1);
		s->frame_offset = -offset;
	}
	ctx->frame.slot_area_size = cast(u32)offset;

	if (order) gb_free(heap_allocator(), order);

	// Spill area: next_value * 8 bytes below slot area
	u32 spill_bytes = p->next_value * 8;

	// Total = slot_area + spill_area, aligned to 16
	u32 total = ctx->frame.slot_area_size + spill_bytes;
	total = (total + 15) & ~15u;
	ctx->frame.total_frame_size = total;
}

// Prologue: push rbp / mov rbp, rsp / sub rsp, N
gb_internal void fb_x64_emit_prologue(fbLowCtx *ctx) {
	// push rbp
	fb_low_emit_byte(ctx, 0x55);
	// mov rbp, rsp
	fb_x64_rex(ctx, true, FB_RSP, 0, FB_RBP);
	fb_low_emit_byte(ctx, 0x89);
	fb_x64_modrm(ctx, 0x03, FB_RSP, FB_RBP);

	if (ctx->frame.total_frame_size > 0) {
		i32 frame_size = cast(i32)ctx->frame.total_frame_size;
		fb_x64_rex(ctx, true, 0, 0, FB_RSP);
		if (frame_size <= 127) {
			// sub rsp, imm8 (4 bytes)
			fb_low_emit_byte(ctx, 0x83);
			fb_x64_modrm(ctx, 0x03, 5, FB_RSP); // /5 = SUB
			fb_x64_imm8(ctx, cast(i8)frame_size);
		} else {
			// sub rsp, imm32 (7 bytes)
			fb_low_emit_byte(ctx, 0x81);
			fb_x64_modrm(ctx, 0x03, 5, FB_RSP); // /5 = SUB
			fb_x64_imm32(ctx, frame_size);
		}
	}
}

// Epilogue: mov rsp, rbp / pop rbp / ret
gb_internal void fb_x64_emit_epilogue(fbLowCtx *ctx) {
	// mov rsp, rbp
	fb_x64_rex(ctx, true, FB_RBP, 0, FB_RSP);
	fb_low_emit_byte(ctx, 0x89);
	fb_x64_modrm(ctx, 0x03, FB_RBP, FB_RSP);
	// pop rbp
	fb_low_emit_byte(ctx, 0x5D);
	// ret
	fb_low_emit_byte(ctx, 0xC3);
}

// ───────────────────────────────────────────────────────────────────────
// ALU helper: two-operand pattern (mov rd,ra / OP rd,rb)
// opcode is the primary opcode byte for the reg,reg form (e.g., 0x01 for ADD)
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_alu_rr(fbLowCtx *ctx, fbInst *inst, u8 opcode) {
	fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
	fbX64Reg rb = fb_x64_resolve_gp(ctx, inst->b, (1u << ra));
	fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, cast(u16)((1u << ra) | (1u << rb)));
	if (rd != ra) {
		fb_x64_mov_rr(ctx, rd, ra);
	}
	// OP rd, rb (REX.W opcode modrm)
	fb_x64_rex(ctx, true, rb, 0, rd);
	fb_low_emit_byte(ctx, opcode);
	fb_x64_modrm(ctx, 0x03, rb, rd);
}

// ───────────────────────────────────────────────────────────────────────
// Shift helper: saves/restores RCX, uses CL as shift amount
// ext is the /r field: 4=SHL, 5=SHR, 7=SAR, 0=ROL, 1=ROR
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_shift_cl(fbLowCtx *ctx, fbInst *inst, u8 ext) {
	fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
	fbX64Reg rb = fb_x64_resolve_gp(ctx, inst->b, (1u << ra));

	// Move shift amount into RCX (handles spill, move, and tracking)
	fb_x64_move_value_to_reg(ctx, inst->b, FB_RCX);

	// Allocate dest, excluding both ra and RCX
	fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, cast(u16)((1u << ra) | (1u << FB_RCX)));
	if (rd != ra) {
		fb_x64_mov_rr(ctx, rd, ra);
	}

	// SHL/SHR/SAR/ROL/ROR rd, cl: REX.W D3 /ext
	fb_x64_rex(ctx, true, ext, 0, rd);
	fb_low_emit_byte(ctx, 0xD3);
	fb_x64_modrm(ctx, 0x03, ext, rd);

	// Mark RCX as free (shift amount consumed)
	ctx->gp[FB_RCX].vreg = FB_NOREG;
}

// ───────────────────────────────────────────────────────────────────────
// Division helper: uses RAX:RDX pair
// is_signed: true for IDIV/CQO, false for DIV/XOR RDX
// want_remainder: true for MOD (result in RDX), false for DIV (result in RAX)
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_div(fbLowCtx *ctx, fbInst *inst, bool is_signed, bool want_remainder) {
	u16 rax_rdx_mask = cast(u16)((1u << FB_RAX) | (1u << FB_RDX));

	// Resolve divisor first, avoiding RAX/RDX
	fbX64Reg rb = fb_x64_resolve_gp(ctx, inst->b, 0);

	// If divisor landed in RAX or RDX, move it to a safe register
	if (rb == FB_RAX || rb == FB_RDX) {
		fbX64Reg safe = fb_x64_alloc_gp(ctx, FB_NOREG, rax_rdx_mask);
		fb_x64_mov_rr(ctx, safe, rb);
		ctx->gp[rb].vreg = FB_NOREG;
		ctx->gp[safe].vreg = inst->b;
		ctx->gp[safe].last_use = ctx->current_inst_idx;
		ctx->gp[safe].dirty = true;
		ctx->value_loc[inst->b] = cast(i32)safe;
		rb = safe;
	}

	// Now safe to spill RAX and RDX (divisor is elsewhere)
	fb_x64_spill_reg(ctx, FB_RAX);
	fb_x64_spill_reg(ctx, FB_RDX);

	// Move dividend into RAX
	fb_x64_move_value_to_reg(ctx, inst->a, FB_RAX);

	// Sign/zero extend into RDX
	if (is_signed) {
		// CQO: sign-extend RAX into RDX:RAX
		fb_x64_rex(ctx, true, 0, 0, 0);
		fb_low_emit_byte(ctx, 0x99);
	} else {
		// xor edx, edx (2 bytes, zero-extends to 64, dependency-breaking)
		fb_x64_rex_if_needed(ctx, false, FB_RDX, 0, FB_RDX);
		fb_low_emit_byte(ctx, 0x31);
		fb_x64_modrm(ctx, 0x03, FB_RDX, FB_RDX);
	}
	ctx->gp[FB_RDX].vreg = FB_NOREG; // RDX is now part of dividend, not a user value

	// IDIV/DIV rb: REX.W F7 /7 (IDIV) or /6 (DIV)
	u8 ext = is_signed ? 7 : 6;
	fb_x64_rex(ctx, true, ext, 0, rb);
	fb_low_emit_byte(ctx, 0xF7);
	fb_x64_modrm(ctx, 0x03, ext, rb);

	// Result is in RAX (quotient) or RDX (remainder)
	fbX64Reg result_reg = want_remainder ? FB_RDX : FB_RAX;
	fbX64Reg other_reg  = want_remainder ? FB_RAX : FB_RDX;

	// The non-result register is now dead
	ctx->gp[other_reg].vreg = FB_NOREG;
	ctx->gp[other_reg].dirty = false;
	// RAX no longer holds the dividend
	if (ctx->value_loc[inst->a] == cast(i32)FB_RAX) {
		ctx->value_loc[inst->a] = fb_x64_spill_offset(ctx, inst->a);
	}

	// Assign result
	ctx->gp[result_reg].vreg = inst->r;
	ctx->gp[result_reg].last_use = ctx->current_inst_idx;
	ctx->gp[result_reg].dirty = true;
	ctx->value_loc[inst->r] = cast(i32)result_reg;
}

// ───────────────────────────────────────────────────────────────────────
// Branch fixup recording
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_record_fixup(fbLowCtx *ctx, u32 code_offset, u32 target_block) {
	if (ctx->fixup_count >= ctx->fixup_cap) {
		u32 new_cap = ctx->fixup_cap * 2;
		if (new_cap < 16) new_cap = 16;
		ctx->fixups = gb_resize_array(heap_allocator(), ctx->fixups, ctx->fixup_cap, new_cap);
		ctx->fixup_cap = new_cap;
	}
	fbFixup *f = &ctx->fixups[ctx->fixup_count++];
	f->code_offset  = code_offset;
	f->target_block = target_block;
}

// Emit jmp rel32 to target_block.
// current_bi: index of the block currently being lowered (blocks < current_bi are already emitted)
gb_internal void fb_x64_emit_jmp(fbLowCtx *ctx, u32 target_block, u32 current_bi) {
	fb_low_emit_byte(ctx, 0xE9);
	u32 disp_offset = ctx->code_count;
	if (target_block <= current_bi) {
		// Backward jump: target block already emitted, compute displacement
		i32 disp = cast(i32)ctx->block_offsets[target_block] - cast(i32)(disp_offset + 4);
		fb_x64_imm32(ctx, disp);
	} else {
		// Forward jump: placeholder, record fixup
		fb_x64_imm32(ctx, 0);
		fb_x64_record_fixup(ctx, disp_offset, target_block);
	}
}

// Emit jcc rel32 (near conditional jump) to target_block.
// cc is the x86 condition code (0x4=E, 0x5=NE, etc.)
gb_internal void fb_x64_emit_jcc(fbLowCtx *ctx, u8 cc, u32 target_block, u32 current_bi) {
	fb_low_emit_byte(ctx, 0x0F);
	fb_low_emit_byte(ctx, cast(u8)(0x80 + cc));
	u32 disp_offset = ctx->code_count;
	if (target_block <= current_bi) {
		i32 disp = cast(i32)ctx->block_offsets[target_block] - cast(i32)(disp_offset + 4);
		fb_x64_imm32(ctx, disp);
	} else {
		fb_x64_imm32(ctx, 0);
		fb_x64_record_fixup(ctx, disp_offset, target_block);
	}
}

// ───────────────────────────────────────────────────────────────────────
// Comparison helper: maps FB_CMP_* opcode to x86 condition code (0x4=E, 0x5=NE, etc.)
// Used with SETcc (0F 90+cc), Jcc (0F 80+cc), and CMOVcc (0F 40+cc).
// ───────────────────────────────────────────────────────────────────────

gb_internal u8 fb_x64_cmp_to_cc(fbOp op) {
	switch (op) {
	case FB_CMP_EQ:  return 0x4;  // E  (equal)
	case FB_CMP_NE:  return 0x5;  // NE (not equal)
	case FB_CMP_SLT: return 0xC;  // L  (less, signed)
	case FB_CMP_SLE: return 0xE;  // LE (less or equal, signed)
	case FB_CMP_SGT: return 0xF;  // G  (greater, signed)
	case FB_CMP_SGE: return 0xD;  // GE (greater or equal, signed)
	case FB_CMP_ULT: return 0x2;  // B  (below, unsigned)
	case FB_CMP_ULE: return 0x6;  // BE (below or equal, unsigned)
	case FB_CMP_UGT: return 0x7;  // A  (above, unsigned)
	case FB_CMP_UGE: return 0x3;  // AE (above or equal, unsigned)
	default: GB_PANIC("unreachable"); return 0;
	}
}

// ───────────────────────────────────────────────────────────────────────
// Procedure lowering
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_lower_proc_x64(fbLowCtx *ctx) {
	fbProc *p = ctx->proc;

	// Initialize value tracking
	fb_x64_init_value_loc(ctx);

	// Compute stack frame layout
	fb_x64_compute_frame(ctx);

	// Emit prologue
	fb_x64_emit_prologue(ctx);

	// Lower each block
	for (u32 bi = 0; bi < p->block_count; bi++) {
		if (ctx->block_offsets) {
			ctx->block_offsets[bi] = ctx->code_count;
		}

		// Reset register state at block start
		fb_x64_reset_regs(ctx);

		fbBlock *blk = &p->blocks[bi];
		for (u32 ii = 0; ii < blk->inst_count; ii++) {
			ctx->current_inst_idx = blk->first_inst + ii;
			fbInst *inst = &p->insts[ctx->current_inst_idx];

			switch (cast(fbOp)inst->op) {

			// ── Constants ──────────────────────────────────────
			case FB_ICONST: {
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, 0);
				i64 val = inst->imm;
				if (val == 0) {
					// xor rd, rd (32-bit clears upper 32)
					fb_x64_rex_if_needed(ctx, false, rd, 0, rd);
					fb_low_emit_byte(ctx, 0x31);
					fb_x64_modrm(ctx, 0x03, rd, rd);
				} else if (val >= INT32_MIN && val <= INT32_MAX) {
					fb_x64_mov_ri32(ctx, rd, cast(i32)val);
				} else if (val >= 0 && val <= cast(i64)UINT32_MAX) {
					// mov r32, imm32 (5 bytes, zero-extends to 64)
					fb_x64_rex_if_needed(ctx, false, 0, 0, rd);
					fb_low_emit_byte(ctx, cast(u8)(0xB8 + (rd & 7)));
					fb_x64_imm32(ctx, cast(i32)val);
				} else {
					fb_x64_mov_ri64(ctx, rd, val);
				}
				break;
			}

			// ── Stack allocation ───────────────────────────────
			case FB_ALLOCA: {
				u32 slot_idx = cast(u32)inst->a;
				GB_ASSERT(slot_idx < p->slot_count);
				i32 frame_off = p->slots[slot_idx].frame_offset;
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, 0);
				// lea rd, [rbp + frame_offset]
				fb_x64_rex(ctx, true, rd, 0, FB_RBP);
				fb_low_emit_byte(ctx, 0x8D);
				fb_x64_modrm_rbp_disp32(ctx, rd, frame_off);
				break;
			}

			// ── Memory ─────────────────────────────────────────
			case FB_LOAD: {
				fbX64Reg rptr = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << rptr));
				fbTypeKind tk = cast(fbTypeKind)(inst->type_raw & 0xFF);

				switch (tk) {
				case FBT_I8:
				case FBT_I1:
					// movzx r32, byte [rptr]: 0F B6 modrm (32-bit dest zero-extends to 64)
					fb_x64_rex_if_needed(ctx, false, rd, 0, rptr);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xB6);
					fb_x64_modrm_indirect(ctx, rd, rptr);
					break;
				case FBT_I16:
					// movzx r32, word [rptr]: 0F B7 modrm (32-bit dest zero-extends to 64)
					fb_x64_rex_if_needed(ctx, false, rd, 0, rptr);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xB7);
					fb_x64_modrm_indirect(ctx, rd, rptr);
					break;
				case FBT_I32:
					// mov rd(32), [rptr]: 8B modrm (zero-extends to 64)
					fb_x64_rex_if_needed(ctx, false, rd, 0, rptr);
					fb_low_emit_byte(ctx, 0x8B);
					fb_x64_modrm_indirect(ctx, rd, rptr);
					break;
				default: // I64, PTR
					// mov rd, [rptr]: REX.W 8B modrm
					fb_x64_rex(ctx, true, rd, 0, rptr);
					fb_low_emit_byte(ctx, 0x8B);
					fb_x64_modrm_indirect(ctx, rd, rptr);
					break;
				}
				break;
			}

			case FB_STORE: {
				fbX64Reg rptr = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rval = fb_x64_resolve_gp(ctx, inst->b, (1u << rptr));
				fbTypeKind tk = cast(fbTypeKind)(inst->type_raw & 0xFF);

				switch (tk) {
				case FBT_I8:
				case FBT_I1:
					// mov byte [rptr], rval(8): REX 88 modrm
					// Always emit REX to access SIL/DIL/SPL/BPL
					fb_x64_rex(ctx, false, rval, 0, rptr);
					fb_low_emit_byte(ctx, 0x88);
					fb_x64_modrm_indirect(ctx, rval, rptr);
					break;
				case FBT_I16:
					// mov word [rptr], rval(16): 66 REX 89 modrm
					fb_low_emit_byte(ctx, 0x66);
					fb_x64_rex_if_needed(ctx, false, rval, 0, rptr);
					fb_low_emit_byte(ctx, 0x89);
					fb_x64_modrm_indirect(ctx, rval, rptr);
					break;
				case FBT_I32:
					// mov dword [rptr], rval(32): 89 modrm
					fb_x64_rex_if_needed(ctx, false, rval, 0, rptr);
					fb_low_emit_byte(ctx, 0x89);
					fb_x64_modrm_indirect(ctx, rval, rptr);
					break;
				default: // I64, PTR
					// mov qword [rptr], rval: REX.W 89 modrm
					fb_x64_rex(ctx, true, rval, 0, rptr);
					fb_low_emit_byte(ctx, 0x89);
					fb_x64_modrm_indirect(ctx, rval, rptr);
					break;
				}
				break;
			}

			// ── Pointer arithmetic ─────────────────────────────
			case FB_MEMBER: {
				i64 offset = inst->imm;
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (offset == 0) {
					if (rd != ra) {
						fb_x64_mov_rr(ctx, rd, ra);
					}
				} else if (offset >= INT32_MIN && offset <= INT32_MAX) {
					// lea rd, [ra + disp32]
					fb_x64_rex(ctx, true, rd, 0, ra);
					fb_low_emit_byte(ctx, 0x8D);
					if ((ra & 7) == FB_RSP) {
						// RSP as base needs SIB
						fb_x64_modrm(ctx, 0x02, rd, 0x04);
						fb_x64_sib(ctx, 0, FB_RSP, FB_RSP);
					} else {
						fb_x64_modrm(ctx, 0x02, rd, ra);
					}
					fb_x64_imm32(ctx, cast(i32)offset);
				} else {
					// Large offset: mov tmp, imm64; add rd, tmp
					fbX64Reg tmp = fb_x64_alloc_gp(ctx, FB_NOREG, cast(u16)((1u << ra) | (1u << rd)));
					fb_x64_mov_ri64(ctx, tmp, offset);
					if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
					fb_x64_rex(ctx, true, tmp, 0, rd);
					fb_low_emit_byte(ctx, 0x01);
					fb_x64_modrm(ctx, 0x03, tmp, rd);
					// Free temp
					ctx->gp[tmp].vreg = FB_NOREG;
				}
				break;
			}

			case FB_ARRAY: {
				fbX64Reg rbase = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg ridx = fb_x64_resolve_gp(ctx, inst->b, (1u << rbase));
				i64 stride = inst->imm;
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, cast(u16)((1u << rbase) | (1u << ridx)));

				// Check if stride is a power of 2 that fits in SIB scale (1,2,4,8)
				u8 scale_bits = 0xFF;
				if (stride == 1) scale_bits = 0;
				else if (stride == 2) scale_bits = 1;
				else if (stride == 4) scale_bits = 2;
				else if (stride == 8) scale_bits = 3;

				if (scale_bits != 0xFF && (ridx & 7) != FB_RSP) {
					// lea rd, [rbase + ridx*scale]
					fb_x64_rex(ctx, true, rd, ridx, rbase);
					fb_low_emit_byte(ctx, 0x8D);
					if ((rbase & 7) == FB_RBP) {
						// RBP base needs mod=01 disp8=0
						fb_x64_modrm(ctx, 0x01, rd, 0x04);
						fb_x64_sib(ctx, scale_bits, ridx, rbase);
						fb_x64_imm8(ctx, 0);
					} else {
						fb_x64_modrm(ctx, 0x00, rd, 0x04);
						fb_x64_sib(ctx, scale_bits, ridx, rbase);
					}
				} else {
					// General case: imul tmp, ridx, stride; lea rd, [rbase + tmp]
					fbX64Reg tmp = fb_x64_alloc_gp(ctx, FB_NOREG, cast(u16)((1u << rbase) | (1u << ridx) | (1u << rd)));
					// imul tmp, ridx, imm32
					fb_x64_rex(ctx, true, tmp, 0, ridx);
					fb_low_emit_byte(ctx, 0x69);
					fb_x64_modrm(ctx, 0x03, tmp, ridx);
					fb_x64_imm32(ctx, cast(i32)stride);

					// lea rd, [rbase + tmp] via add
					if (rd != rbase) fb_x64_mov_rr(ctx, rd, rbase);
					fb_x64_rex(ctx, true, tmp, 0, rd);
					fb_low_emit_byte(ctx, 0x01);
					fb_x64_modrm(ctx, 0x03, tmp, rd);

					ctx->gp[tmp].vreg = FB_NOREG;
				}
				break;
			}

			// ── Integer arithmetic ─────────────────────────────
			case FB_ADD: fb_x64_alu_rr(ctx, inst, 0x01); break; // ADD
			case FB_SUB: fb_x64_alu_rr(ctx, inst, 0x29); break; // SUB
			case FB_AND: fb_x64_alu_rr(ctx, inst, 0x21); break; // AND
			case FB_OR:  fb_x64_alu_rr(ctx, inst, 0x09); break; // OR
			case FB_XOR: fb_x64_alu_rr(ctx, inst, 0x31); break; // XOR

			case FB_MUL: {
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rb = fb_x64_resolve_gp(ctx, inst->b, (1u << ra));
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, cast(u16)((1u << ra) | (1u << rb)));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				// IMUL rd, rb: REX.W 0F AF modrm
				fb_x64_rex(ctx, true, rd, 0, rb);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0xAF);
				fb_x64_modrm(ctx, 0x03, rd, rb);
				break;
			}

			case FB_NEG: {
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				// NEG rd: REX.W F7 /3
				fb_x64_rex(ctx, true, 3, 0, rd);
				fb_low_emit_byte(ctx, 0xF7);
				fb_x64_modrm(ctx, 0x03, 3, rd);
				break;
			}

			case FB_NOT: {
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				// NOT rd: REX.W F7 /2
				fb_x64_rex(ctx, true, 2, 0, rd);
				fb_low_emit_byte(ctx, 0xF7);
				fb_x64_modrm(ctx, 0x03, 2, rd);
				break;
			}

			// ── Shifts & rotates ───────────────────────────────
			case FB_SHL:  fb_x64_shift_cl(ctx, inst, 4); break;
			case FB_LSHR: fb_x64_shift_cl(ctx, inst, 5); break;
			case FB_ASHR: fb_x64_shift_cl(ctx, inst, 7); break;
			case FB_ROL:  fb_x64_shift_cl(ctx, inst, 0); break;
			case FB_ROR:  fb_x64_shift_cl(ctx, inst, 1); break;

			// ── Division & modulo ──────────────────────────────
			case FB_SDIV: fb_x64_div(ctx, inst, true,  false); break;
			case FB_UDIV: fb_x64_div(ctx, inst, false, false); break;
			case FB_SMOD: fb_x64_div(ctx, inst, true,  true);  break;
			case FB_UMOD: fb_x64_div(ctx, inst, false, true);  break;

			// ── Integer comparisons ───────────────────────────
			case FB_CMP_EQ: case FB_CMP_NE:
			case FB_CMP_SLT: case FB_CMP_SLE:
			case FB_CMP_SGT: case FB_CMP_SGE:
			case FB_CMP_ULT: case FB_CMP_ULE:
			case FB_CMP_UGT: case FB_CMP_UGE: {
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rb = fb_x64_resolve_gp(ctx, inst->b, (1u << ra));
				// CMP ra, rb: REX.W 39 /r (sub without storing result)
				fb_x64_rex(ctx, true, rb, 0, ra);
				fb_low_emit_byte(ctx, 0x39);
				fb_x64_modrm(ctx, 0x03, rb, ra);
				// SETcc rd_low: 0F (90+cc) modrm(03, 0, rd)
				// Allocate rd, then emit setcc + movzx.
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, cast(u16)((1u << ra) | (1u << rb)));
				u8 cc = fb_x64_cmp_to_cc(cast(fbOp)inst->op);
				// Must always emit REX for byte-register operands to avoid
				// legacy AH/CH/DH/BH encoding for registers 4-7.
				fb_x64_rex(ctx, false, 0, 0, rd);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, cast(u8)(0x90 + cc));
				fb_x64_modrm(ctx, 0x03, 0, rd);
				// MOVZX r32, r8: 0F B6 modrm (zero-extends to 64 via 32-bit dest)
				fb_x64_rex(ctx, false, rd, 0, rd);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0xB6);
				fb_x64_modrm(ctx, 0x03, rd, rd);
				break;
			}

			// ── Select (conditional move) ─────────────────────
			case FB_SELECT: {
				// cond in a, true_val in b, false_val in c
				fbX64Reg rcond = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rtrue = fb_x64_resolve_gp(ctx, inst->b, (1u << rcond));
				fbX64Reg rfalse = fb_x64_resolve_gp(ctx, inst->c, cast(u16)((1u << rcond) | (1u << rtrue)));
				// TEST cond8, cond8 — must always emit REX for byte-register
				// operands to avoid legacy AH/CH/DH/BH encoding for registers 4-7.
				fb_x64_rex(ctx, false, rcond, 0, rcond);
				fb_low_emit_byte(ctx, 0x84);
				fb_x64_modrm(ctx, 0x03, rcond, rcond);
				// Allocate result
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, cast(u16)((1u << rcond) | (1u << rtrue) | (1u << rfalse)));
				// MOV rd, false_val (default)
				fb_x64_mov_rr(ctx, rd, rfalse);
				// CMOVNZ rd, true_val: REX.W 0F 45 modrm (cmovne)
				fb_x64_rex(ctx, true, rd, 0, rtrue);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x45);
				fb_x64_modrm(ctx, 0x03, rd, rtrue);
				break;
			}

			// Field conventions for control-flow ops:
			//   JUMP:   a=target_block
			//   BRANCH: a=cond, b=true_block, c=false_block
			//   SWITCH: a=key, b=default_block, c=aux_start, imm=case_count
			// ── Control flow ───────────────────────────────────
			case FB_JUMP: {
				u32 target = inst->a;
				// Fallthrough optimization: skip jump if target is the next block
				if (target != bi + 1) {
					fb_x64_emit_jmp(ctx, target, bi);
				}
				break;
			}

			case FB_BRANCH: {
				u32 true_block  = inst->b;
				u32 false_block = inst->c;
				// Identical targets: degenerate to unconditional jump
				if (true_block == false_block) {
					if (true_block != bi + 1) {
						fb_x64_emit_jmp(ctx, true_block, bi);
					}
					break;
				}
				// cond in a, true_block in b, false_block in c
				fbX64Reg rcond = fb_x64_resolve_gp(ctx, inst->a, 0);
				// TEST cond8, cond8 — must always emit REX for byte-register
				// operands to avoid legacy AH/CH/DH/BH encoding for registers 4-7.
				fb_x64_rex(ctx, false, rcond, 0, rcond);
				fb_low_emit_byte(ctx, 0x84);
				fb_x64_modrm(ctx, 0x03, rcond, rcond);

				if (false_block == bi + 1) {
					// False is fallthrough: jnz true_block
					fb_x64_emit_jcc(ctx, 0x5, true_block, bi); // 0x5 = JNE/JNZ
				} else if (true_block == bi + 1) {
					// True is fallthrough: jz false_block
					fb_x64_emit_jcc(ctx, 0x4, false_block, bi); // 0x4 = JE/JZ
				} else {
					// Neither is fallthrough: jnz true + jmp false
					fb_x64_emit_jcc(ctx, 0x5, true_block, bi);
					fb_x64_emit_jmp(ctx, false_block, bi);
				}
				break;
			}

			case FB_SWITCH: {
				// key in a, default_block in b, cases in aux
				fbX64Reg rkey = fb_x64_resolve_gp(ctx, inst->a, 0);
				u32 default_block = inst->b;
				u32 aux_start = inst->c;
				u32 case_count = cast(u32)inst->imm;
				// Each case is 2 aux entries: [value, block]
				for (u32 ci = 0; ci < case_count; ci++) {
					i64 case_val = cast(i64)cast(i32)p->aux[aux_start + ci * 2];
					u32 case_block = p->aux[aux_start + ci * 2 + 1];
					// CMP rkey, imm32: REX.W 81 /7 imm32
					fb_x64_rex(ctx, true, 7, 0, rkey);
					fb_low_emit_byte(ctx, 0x81);
					fb_x64_modrm(ctx, 0x03, 7, rkey);
					fb_x64_imm32(ctx, cast(i32)case_val);
					// JE case_block
					fb_x64_emit_jcc(ctx, 0x4, case_block, bi);
				}
				// JMP default_block
				if (default_block != bi + 1) {
					fb_x64_emit_jmp(ctx, default_block, bi);
				}
				break;
			}

			case FB_RET:
				fb_x64_emit_epilogue(ctx);
				break;

			case FB_UNREACHABLE:
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x0B);
				break;

			case FB_TRAP:
			case FB_DEBUGBREAK:
				fb_low_emit_byte(ctx, 0xCC);
				break;

			default:
				// Unimplemented opcode — emit ud2 as trap
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x0B);
				break;
			}
		}
	}

	// Patch forward branch fixups
	for (u32 fi = 0; fi < ctx->fixup_count; fi++) {
		fbFixup *f = &ctx->fixups[fi];
		GB_ASSERT(f->target_block < p->block_count);
		i32 disp = cast(i32)ctx->block_offsets[f->target_block] - cast(i32)(f->code_offset + 4);
		ctx->code[f->code_offset + 0] = cast(u8)(disp & 0xFF);
		ctx->code[f->code_offset + 1] = cast(u8)((disp >> 8) & 0xFF);
		ctx->code[f->code_offset + 2] = cast(u8)((disp >> 16) & 0xFF);
		ctx->code[f->code_offset + 3] = cast(u8)((disp >> 24) & 0xFF);
	}
}

gb_internal void fb_lower_all(fbModule *m) {
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign) {
			continue;
		}

		fbLowCtx ctx = {};
		ctx.proc   = p;
		ctx.module = m;

		if (p->block_count > 0) {
			ctx.block_offsets = gb_alloc_array(heap_allocator(), u32, p->block_count);
		}

		switch (m->target.arch) {
		case FB_ARCH_X64:
			fb_lower_proc_x64(&ctx);
			break;
		default:
			GB_PANIC("fast backend: unsupported architecture for lowering");
			break;
		}

		p->machine_code_size = ctx.code_count;
		if (ctx.code_count > 0) {
			p->machine_code = gb_alloc_array(heap_allocator(), u8, ctx.code_count);
			gb_memmove(p->machine_code, ctx.code, ctx.code_count);
		}

		if (ctx.code)           gb_free(heap_allocator(), ctx.code);
		if (ctx.block_offsets)  gb_free(heap_allocator(), ctx.block_offsets);
		if (ctx.value_loc)      gb_free(heap_allocator(), ctx.value_loc);
		if (ctx.fixups)         gb_free(heap_allocator(), ctx.fixups);
	}
}
