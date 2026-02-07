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
	u32 needed = ctx->code_count + count;
	if (needed > ctx->code_cap) {
		u32 new_cap = ctx->code_cap * 2;
		if (new_cap < needed) new_cap = needed;
		if (new_cap < 256) new_cap = 256;
		ctx->code = gb_resize_array(heap_allocator(), ctx->code, ctx->code_cap, new_cap);
		ctx->code_cap = new_cap;
	}
	gb_memmove(ctx->code + ctx->code_count, bytes, count);
	ctx->code_count += count;
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

// SysV AMD64 ABI: integer/pointer argument registers in order
gb_global fbX64Reg const fb_x64_sysv_arg_regs[] = {
	FB_RDI, FB_RSI, FB_RDX, FB_RCX, FB_R8, FB_R9,
};
gb_global u32 const FB_X64_SYSV_ARG_COUNT = gb_count_of(fb_x64_sysv_arg_regs);

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
// XMM encoding helpers (scratch XMM0/XMM1 for float ops)
// ───────────────────────────────────────────────────────────────────────

// XMM register indices (0 = XMM0, 1 = XMM1, etc.)
enum : u8 { FB_XMM0 = 0, FB_XMM1 = 1 };

// MOVD xmm, r32: 66 [REX] 0F 6E /r (32-bit GP→XMM)
gb_internal void fb_x64_movd_gp_to_xmm(fbLowCtx *ctx, u8 xmm, fbX64Reg gp) {
	fb_low_emit_byte(ctx, 0x66);
	fb_x64_rex_if_needed(ctx, false, xmm, 0, gp);
	fb_low_emit_byte(ctx, 0x0F);
	fb_low_emit_byte(ctx, 0x6E);
	fb_x64_modrm(ctx, 0x03, xmm, gp);
}

// MOVQ xmm, r64: 66 REX.W 0F 6E /r (64-bit GP→XMM)
gb_internal void fb_x64_movq_gp_to_xmm(fbLowCtx *ctx, u8 xmm, fbX64Reg gp) {
	fb_low_emit_byte(ctx, 0x66);
	fb_x64_rex(ctx, true, xmm, 0, gp);
	fb_low_emit_byte(ctx, 0x0F);
	fb_low_emit_byte(ctx, 0x6E);
	fb_x64_modrm(ctx, 0x03, xmm, gp);
}

// MOVD r32, xmm: 66 [REX] 0F 7E /r (32-bit XMM→GP)
gb_internal void fb_x64_movd_xmm_to_gp(fbLowCtx *ctx, fbX64Reg gp, u8 xmm) {
	fb_low_emit_byte(ctx, 0x66);
	fb_x64_rex_if_needed(ctx, false, xmm, 0, gp);
	fb_low_emit_byte(ctx, 0x0F);
	fb_low_emit_byte(ctx, 0x7E);
	fb_x64_modrm(ctx, 0x03, xmm, gp);
}

// MOVQ r64, xmm: 66 REX.W 0F 7E /r (64-bit XMM→GP)
gb_internal void fb_x64_movq_xmm_to_gp(fbLowCtx *ctx, fbX64Reg gp, u8 xmm) {
	fb_low_emit_byte(ctx, 0x66);
	fb_x64_rex(ctx, true, xmm, 0, gp);
	fb_low_emit_byte(ctx, 0x0F);
	fb_low_emit_byte(ctx, 0x7E);
	fb_x64_modrm(ctx, 0x03, xmm, gp);
}

// Generic SSE reg,reg: prefix 0F opcode ModRM(11, xmm_dst, xmm_src)
gb_internal void fb_x64_sse_rr(fbLowCtx *ctx, u8 prefix, u8 opcode, u8 xmm_dst, u8 xmm_src) {
	fb_low_emit_byte(ctx, prefix);
	fb_low_emit_byte(ctx, 0x0F);
	fb_low_emit_byte(ctx, opcode);
	fb_x64_modrm(ctx, 0x03, xmm_dst, xmm_src);
}

// Move GP register value to XMM0 or XMM1, dispatching on type kind
gb_internal void fb_x64_gp_to_xmm(fbLowCtx *ctx, fbX64Reg gp, u8 xmm, fbTypeKind tk) {
	if (tk == FBT_F32) {
		fb_x64_movd_gp_to_xmm(ctx, xmm, gp);
	} else {
		fb_x64_movq_gp_to_xmm(ctx, xmm, gp);
	}
}

// Move XMM0 result back to GP register, dispatching on type kind
gb_internal void fb_x64_xmm_to_gp(fbLowCtx *ctx, fbX64Reg gp, u8 xmm, fbTypeKind tk) {
	if (tk == FBT_F32) {
		fb_x64_movd_xmm_to_gp(ctx, gp, xmm);
	} else {
		fb_x64_movq_xmm_to_gp(ctx, gp, xmm);
	}
}

// ───────────────────────────────────────────────────────────────────────
// Register allocator
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_spill_reg(fbLowCtx *ctx, fbX64Reg reg);
gb_internal i32  fb_x64_spill_offset(fbLowCtx *ctx, u32 vreg);
gb_internal void fb_x64_record_reloc(fbLowCtx *ctx, u32 code_offset, u32 target_proc, i64 addend, fbRelocType reloc_type);

// Emit RIP-relative LEA for a symbol: lea reg, [rip+disp32] + relocation record.
// Used by both resolve_gp (which picks any free register) and move_value_to_reg
// (which targets a specific register).
gb_internal void fb_x64_emit_lea_sym(fbLowCtx *ctx, fbX64Reg reg, u32 sym_idx) {
	fb_x64_rex(ctx, true, reg, 0, 5); // rm=5 for RIP-relative
	fb_low_emit_byte(ctx, 0x8D);
	fb_x64_modrm(ctx, 0x00, reg, 5); // mod=00 rm=5 → [RIP+disp32]
	u32 disp_offset = ctx->code_count;
	fb_x64_imm32(ctx, 0); // placeholder
	fb_x64_record_reloc(ctx, disp_offset, sym_idx, -4, FB_RELOC_PC32);
}

// Spill all dirty registers and clear register state.
// Emits store instructions for dirty values so they are on the stack
// before control flow diverges. Call this BEFORE each terminator.
gb_internal void fb_x64_reset_regs(fbLowCtx *ctx) {
	for (u32 i = 0; i < FB_X64_GP_ALLOC_COUNT; i++) {
		fbX64Reg r = fb_x64_gp_alloc_order[i];
		u32 vreg = ctx->gp[r].vreg;
		if (vreg == FB_NOREG) continue;
		if (ctx->gp[r].dirty) {
			fb_x64_spill_reg(ctx, r);
		} else {
			ctx->value_loc[vreg] = fb_x64_spill_offset(ctx, vreg);
			ctx->gp[r].vreg = FB_NOREG;
		}
	}
	for (int i = 0; i < 16; i++) {
		ctx->gp[i].vreg     = FB_NOREG;
		ctx->gp[i].last_use = 0;
		ctx->gp[i].dirty    = false;
	}
}

// Clear register bookkeeping at block entry WITHOUT emitting code.
// All values must already be on the stack (spilled by reset_regs before
// the previous block's terminator). This just resets the allocator state
// for the new block.
gb_internal void fb_x64_clear_reg_state(fbLowCtx *ctx) {
	for (u32 i = 0; i < FB_X64_GP_ALLOC_COUNT; i++) {
		fbX64Reg r = fb_x64_gp_alloc_order[i];
		u32 vreg = ctx->gp[r].vreg;
		if (vreg != FB_NOREG) {
			// Value was loaded by the previous block's terminator
			// (e.g. BRANCH condition). The spill slot is still valid
			// because it was written before the terminator ran.
			ctx->value_loc[vreg] = fb_x64_spill_offset(ctx, vreg);
		}
	}
	for (int i = 0; i < 16; i++) {
		ctx->gp[i].vreg     = FB_NOREG;
		ctx->gp[i].last_use = 0;
		ctx->gp[i].dirty    = false;
	}
}

gb_internal bool fb_x64_is_terminator(u8 op) {
	return op == FB_JUMP || op == FB_BRANCH || op == FB_RET ||
	       op == FB_UNREACHABLE || op == FB_SWITCH ||
	       op == FB_TRAP;
}

gb_internal void fb_x64_init_value_loc(fbLowCtx *ctx) {
	u32 count = ctx->proc->next_value;
	ctx->value_loc_count = count;
	if (count > 0) {
		ctx->value_loc = gb_alloc_array(heap_allocator(), i32, count);
		ctx->value_sym = gb_alloc_array(heap_allocator(), u32, count);
		for (u32 i = 0; i < count; i++) {
			ctx->value_loc[i] = FB_LOC_NONE;
			ctx->value_sym[i] = FB_NOREG;
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

	// Symbol materialization: SYMADDR values have no register or spill slot,
	// only a symbol reference. Materialize via lea reg, [rip+disp32].
	if (loc == FB_LOC_NONE && ctx->value_sym && ctx->value_sym[vreg] != FB_NOREG) {
		fbX64Reg r = fb_x64_alloc_gp(ctx, vreg, exclude_mask);
		fb_x64_emit_lea_sym(ctx, r, ctx->value_sym[vreg]);
		return r;
	}

	// Spilled — allocate and reload
	GB_ASSERT_MSG(loc != FB_LOC_NONE,
		"fb_x64_resolve_gp: value %u has no location and no symbol reference", vreg);
	fbX64Reg r = fb_x64_alloc_gp(ctx, vreg, exclude_mask);
	// Reload from spill slot: mov reg, [rbp+disp32]
	fb_x64_rex(ctx, true, r, 0, FB_RBP);
	fb_low_emit_byte(ctx, 0x8B);
	fb_x64_modrm_rbp_disp32(ctx, r, loc);
	ctx->gp[r].dirty = false; // just loaded, matches memory
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
	} else if (ctx->value_sym && ctx->value_sym[vreg] != FB_NOREG) {
		// SYMADDR value — materialize via RIP-relative LEA
		fb_x64_emit_lea_sym(ctx, target, ctx->value_sym[vreg]);
	} else {
		GB_PANIC("fb_x64_move_value_to_reg: value %u has no location and no symbol", vreg);
	}

	ctx->gp[target].vreg     = vreg;
	ctx->gp[target].last_use = ctx->current_inst_idx;
	ctx->gp[target].dirty    = (loc >= 0 || loc == FB_LOC_NONE); // clean only when reloaded from spill slot
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

	// Store incoming ABI register parameters to their stack slots.
	// Each param_locs entry maps one GP register to a slot + sub_offset.
	// Two-eightbyte params (string, slice) share a single 16-byte slot
	// across two entries (sub_offset 0 and 8).
	fbProc *p = ctx->proc;
	for (u32 i = 0; i < p->param_count && i < FB_X64_SYSV_ARG_COUNT; i++) {
		u32 slot_idx   = p->param_locs[i].slot_idx;
		i32 sub_offset = p->param_locs[i].sub_offset;
		GB_ASSERT(slot_idx < p->slot_count);
		fbStackSlot *s = &p->slots[slot_idx];
		// mov qword [rbp+disp32], reg: REX.W 89 modrm
		fb_x64_rex(ctx, true, fb_x64_sysv_arg_regs[i], 0, FB_RBP);
		fb_low_emit_byte(ctx, 0x89);
		fb_x64_modrm_rbp_disp32(ctx, fb_x64_sysv_arg_regs[i], s->frame_offset + sub_offset);
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

	// Spill RCX so value_loc[inst->b] points to the spill slot, not
	// the register we're about to free.  fb_x64_spill_reg writes the
	// value back if dirty, and always updates value_loc + clears gp[].
	fb_x64_spill_reg(ctx, FB_RCX);
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

	// Move dividend into RAX, then detach it so DIV's clobber doesn't
	// leave value_loc pointing at an unwritten spill slot.
	fb_x64_move_value_to_reg(ctx, inst->a, FB_RAX);
	if (ctx->gp[FB_RAX].dirty) {
		// Flush to spill slot so the value survives if needed later.
		i32 offset = fb_x64_spill_offset(ctx, inst->a);
		fb_x64_rex(ctx, true, FB_RAX, 0, FB_RBP);
		fb_low_emit_byte(ctx, 0x89);
		fb_x64_modrm_rbp_disp32(ctx, FB_RAX, offset);
		ctx->gp[FB_RAX].dirty = false;
	}
	ctx->value_loc[inst->a] = fb_x64_spill_offset(ctx, inst->a);
	ctx->gp[FB_RAX].vreg = FB_NOREG;

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

	// Assign result
	ctx->gp[result_reg].vreg = inst->r;
	ctx->gp[result_reg].last_use = ctx->current_inst_idx;
	ctx->gp[result_reg].dirty = true;
	ctx->value_loc[inst->r] = cast(i32)result_reg;
}

// ───────────────────────────────────────────────────────────────────────
// Float binary arithmetic helper: GP→XMM0/1, SSE op, XMM0→GP
// sse_opcode: 0x58=add, 0x5C=sub, 0x59=mul, 0x5E=div, 0x5D=min, 0x5F=max
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_float_binop(fbLowCtx *ctx, fbInst *inst, u8 sse_opcode) {
	fbTypeKind tk = cast(fbTypeKind)(inst->type_raw & 0xFF);
	u8 prefix = (tk == FBT_F32) ? 0xF3 : 0xF2;

	fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
	fbX64Reg rb = fb_x64_resolve_gp(ctx, inst->b, (1u << ra));

	fb_x64_gp_to_xmm(ctx, ra, FB_XMM0, tk);
	fb_x64_gp_to_xmm(ctx, rb, FB_XMM1, tk);

	// SSE op xmm0, xmm1
	fb_x64_sse_rr(ctx, prefix, sse_opcode, FB_XMM0, FB_XMM1);

	fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, cast(u16)((1u << ra) | (1u << rb)));
	fb_x64_xmm_to_gp(ctx, rd, FB_XMM0, tk);
}

// ───────────────────────────────────────────────────────────────────────
// Float comparison NaN-safe helper: setcc + set{np,p} + {and,or}
//
// UCOMISS/UCOMISD set PF=1 for NaN. Four of the six float comparisons
// need a two-SETcc sequence to account for this:
//   FEQ: sete  + setnp + AND  (ordered and equal)
//   FNE: setne + setp  + OR   (unordered or not-equal)
//   FLT: setb  + setnp + AND  (ordered and below)
//   FLE: setbe + setnp + AND  (ordered and below-or-equal)
//
// FLAGS are preserved across alloc_gp (which only emits MOV for spills).
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_float_cmp_nan_safe(
	fbLowCtx *ctx, fbX64Reg rd,
	u8 setcc_byte, u8 set_parity_byte, u8 combine_byte,
	u16 exclude_mask)
{
	// setcc rd
	fb_x64_rex(ctx, false, 0, 0, rd);
	fb_low_emit_byte(ctx, 0x0F);
	fb_low_emit_byte(ctx, setcc_byte);
	fb_x64_modrm(ctx, 0x03, 0, rd);
	// set{np,p} tmp
	fbX64Reg tmp = fb_x64_alloc_gp(ctx, FB_NOREG, exclude_mask | cast(u16)(1u << rd));
	fb_x64_rex(ctx, false, 0, 0, tmp);
	fb_low_emit_byte(ctx, 0x0F);
	fb_low_emit_byte(ctx, set_parity_byte);
	fb_x64_modrm(ctx, 0x03, 0, tmp);
	// {and,or} rd_byte, tmp_byte
	fb_x64_rex(ctx, false, tmp, 0, rd);
	fb_low_emit_byte(ctx, combine_byte);
	fb_x64_modrm(ctx, 0x03, tmp, rd);
	ctx->gp[tmp].vreg = FB_NOREG;
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

// ───────────────────────────────────────────────────────────────────────
// Call relocation recording
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_x64_record_reloc(fbLowCtx *ctx, u32 code_offset, u32 target_proc, i64 addend, fbRelocType reloc_type) {
	if (ctx->reloc_count >= ctx->reloc_cap) {
		u32 new_cap = ctx->reloc_cap * 2;
		if (new_cap < 16) new_cap = 16;
		ctx->relocs = gb_resize_array(heap_allocator(), ctx->relocs, ctx->reloc_cap, new_cap);
		ctx->reloc_cap = new_cap;
	}
	fbReloc *r = &ctx->relocs[ctx->reloc_count++];
	r->code_offset = code_offset;
	r->target_proc = target_proc;
	r->addend      = addend;
	r->reloc_type  = reloc_type;
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

	// Initialize register state (fbLowCtx is zero-init'd, but gp[i].vreg
	// must be FB_NOREG, not 0, to avoid stale register claims)
	for (int i = 0; i < 16; i++) {
		ctx->gp[i].vreg     = FB_NOREG;
		ctx->gp[i].last_use = 0;
		ctx->gp[i].dirty    = false;
	}

	// Compute stack frame layout
	fb_x64_compute_frame(ctx);

	// Emit prologue
	fb_x64_emit_prologue(ctx);

	// Lower each block
	for (u32 bi = 0; bi < p->block_count; bi++) {
		if (ctx->block_offsets) {
			ctx->block_offsets[bi] = ctx->code_count;
		}

		// Clear register bookkeeping at block entry (no code emission).
		// All values are already on the stack — spilled by reset_regs
		// before the previous block's terminator.
		fb_x64_clear_reg_state(ctx);

		fbBlock *blk = &p->blocks[bi];
		for (u32 ii = 0; ii < blk->inst_count; ii++) {
			ctx->current_inst_idx = blk->first_inst + ii;
			fbInst *inst = &p->insts[ctx->current_inst_idx];

			// Before terminators: spill all dirty registers so
			// values are on the stack before control flow diverges.
			if (fb_x64_is_terminator(inst->op)) {
				fb_x64_reset_regs(ctx);
			}

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

			// Float bit patterns in imm are loaded into GP registers the same as integers
			case FB_FCONST: {
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, 0);
				i64 val = inst->imm;
				if (val == 0) {
					fb_x64_rex_if_needed(ctx, false, rd, 0, rd);
					fb_low_emit_byte(ctx, 0x31);
					fb_x64_modrm(ctx, 0x03, rd, rd);
				} else if (val >= INT32_MIN && val <= INT32_MAX) {
					fb_x64_mov_ri32(ctx, rd, cast(i32)val);
				} else if (val >= 0 && val <= cast(i64)UINT32_MAX) {
					fb_x64_rex_if_needed(ctx, false, 0, 0, rd);
					fb_low_emit_byte(ctx, cast(u8)(0xB8 + (rd & 7)));
					fb_x64_imm32(ctx, cast(i32)val);
				} else {
					fb_x64_mov_ri64(ctx, rd, val);
				}
				break;
			}

			// ── Stack allocation ───────────────────────────────
			// ── Symbol address (deferred materialization) ────
			case FB_SYMADDR: {
				// Record the symbol reference; do NOT allocate a register or emit code.
				// If CALL uses this value, it emits a direct call rel32.
				// If any other instruction uses it, resolve_gp materializes via lea [rip+disp32].
				u32 proc_idx = cast(u32)inst->imm;
				ctx->value_sym[inst->r] = proc_idx;
				// value_loc stays FB_LOC_NONE — resolve_gp checks value_sym
				break;
			}

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
				case FBT_F32:
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
				case FBT_F32:
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

			// ── Memory zeroing ─────────────────────────────────
			case FB_MEMZERO: {
				// rep stosb: RDI=dst, RCX=size, AL=0
				// Encoding: a=dst, b=size_value, imm=alignment

				// Spill whatever was in RDI, RCX, RAX
				fb_x64_spill_reg(ctx, FB_RDI);
				fb_x64_spill_reg(ctx, FB_RCX);
				fb_x64_spill_reg(ctx, FB_RAX);

				// Load dst into RDI, size into RCX
				fb_x64_move_value_to_reg(ctx, inst->a, FB_RDI);
				fb_x64_move_value_to_reg(ctx, inst->b, FB_RCX);

				// Spill operand values to stack so value_loc is consistent
				// after the rep instruction clobbers these registers.
				// Physical register contents are preserved for the rep.
				fb_x64_spill_reg(ctx, FB_RDI);
				fb_x64_spill_reg(ctx, FB_RCX);

				// xor eax, eax (AL=0)
				fb_x64_rex_if_needed(ctx, false, FB_RAX, 0, FB_RAX);
				fb_low_emit_byte(ctx, 0x31);
				fb_x64_modrm(ctx, 0x03, FB_RAX, FB_RAX);

				// rep stosb: F3 AA
				fb_low_emit_byte(ctx, 0xF3);
				fb_low_emit_byte(ctx, 0xAA);
				break;
			}

			// ── Memory copy ───────────────────────────────────
			case FB_MEMCPY: {
				// rep movsb: RDI=dst, RSI=src, RCX=size
				// Encoding: a=dst, b=src, c=size_value, imm=alignment

				// Spill whatever was in RDI, RSI, RCX
				fb_x64_spill_reg(ctx, FB_RDI);
				fb_x64_spill_reg(ctx, FB_RSI);
				fb_x64_spill_reg(ctx, FB_RCX);

				// Load dst, src, size into the required registers
				fb_x64_move_value_to_reg(ctx, inst->a, FB_RDI);
				fb_x64_move_value_to_reg(ctx, inst->b, FB_RSI);
				fb_x64_move_value_to_reg(ctx, inst->c, FB_RCX);

				// Spill operand values to stack so value_loc is consistent
				// after the rep instruction clobbers these registers.
				// Physical register contents are preserved for the rep.
				fb_x64_spill_reg(ctx, FB_RDI);
				fb_x64_spill_reg(ctx, FB_RSI);
				fb_x64_spill_reg(ctx, FB_RCX);

				// rep movsb: F3 A4
				fb_low_emit_byte(ctx, 0xF3);
				fb_low_emit_byte(ctx, 0xA4);
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

			// ── Function calls ────────────────────────────────
			case FB_CALL: {
				// CALL: a = target_value_id, b = aux_start, c = arg_count, flags = calling_convention
				u32 target = inst->a;
				u32 aux_start = inst->b;
				u32 arg_count = inst->c;

				// 1. Spill all occupied caller-saved registers
				for (u32 ri = 0; ri < FB_X64_GP_ALLOC_COUNT; ri++) {
					fbX64Reg r = fb_x64_gp_alloc_order[ri];
					if (ctx->gp[r].vreg != FB_NOREG) {
						fb_x64_spill_reg(ctx, r);
					}
				}

				// 2. Count stack args and compute alignment padding
				u32 reg_args = arg_count < FB_X64_SYSV_ARG_COUNT ? arg_count : FB_X64_SYSV_ARG_COUNT;
				u32 stack_arg_count = arg_count > FB_X64_SYSV_ARG_COUNT ? arg_count - FB_X64_SYSV_ARG_COUNT : 0;
				u32 stack_padding = (stack_arg_count & 1) ? 8 : 0; // 16-byte alignment

				// 3. Adjust stack for alignment padding
				if (stack_padding > 0) {
					// sub rsp, 8
					fb_x64_rex(ctx, true, 0, 0, FB_RSP);
					fb_low_emit_byte(ctx, 0x83);
					fb_x64_modrm(ctx, 0x03, 5, FB_RSP);
					fb_x64_imm8(ctx, 8);
				}

				// 4. Push stack args in reverse order (from spill slots)
				for (u32 ai = arg_count; ai > FB_X64_SYSV_ARG_COUNT; ai--) {
					u32 arg_vreg = p->aux[aux_start + (ai - 1)];
					i32 arg_loc = ctx->value_loc[arg_vreg];
					if (arg_loc >= 0 && arg_loc < 16) {
						// Value is in a register — push reg
						fb_x64_rex_if_needed(ctx, false, 0, 0, cast(u8)arg_loc);
						fb_low_emit_byte(ctx, cast(u8)(0x50 + (arg_loc & 7)));
					} else {
						// Value is on the stack — push qword [rbp+offset]
						i32 offset = (arg_loc != FB_LOC_NONE) ? arg_loc : fb_x64_spill_offset(ctx, arg_vreg);
						fb_x64_rex_if_needed(ctx, false, 6, 0, FB_RBP);
						fb_low_emit_byte(ctx, 0xFF);
						fb_x64_modrm_rbp_disp32(ctx, 6, offset); // /6 = PUSH
					}
				}

				// 5. Load register args into ABI-mandated registers.
				//
				// IMPORTANT: After spill-all (step 1), gp[] is cleared and all values
				// reside in spill slots. This loop loads values from spill slots into
				// fixed argument registers WITHOUT updating gp[] or value_loc[],
				// because these registers are caller-saved and will be clobbered by
				// the callee. No register allocation may occur between this loop
				// and the call instruction emission in step 6.
				for (u32 ai = 0; ai < reg_args; ai++) {
					u32 arg_vreg = p->aux[aux_start + ai];
					fbX64Reg dest = fb_x64_sysv_arg_regs[ai];
					i32 arg_loc = ctx->value_loc[arg_vreg];
					if (arg_loc >= 0 && arg_loc < 16 && cast(fbX64Reg)arg_loc == dest) {
						// Already in the right register (unlikely after spill-all, but handle it)
						continue;
					}
					if (arg_loc >= 0 && arg_loc < 16) {
						// In another register — mov
						fb_x64_mov_rr(ctx, dest, cast(fbX64Reg)arg_loc);
					} else {
						// On stack — reload
						i32 offset = (arg_loc != FB_LOC_NONE) ? arg_loc : fb_x64_spill_offset(ctx, arg_vreg);
						fb_x64_rex(ctx, true, dest, 0, FB_RBP);
						fb_low_emit_byte(ctx, 0x8B);
						fb_x64_modrm_rbp_disp32(ctx, dest, offset);
					}
				}

				// 6. Emit call instruction
				if (ctx->value_sym && ctx->value_sym[target] != FB_NOREG) {
					// Direct call: call rel32 with PLT32 relocation
					fb_low_emit_byte(ctx, 0xE8);
					u32 disp_offset = ctx->code_count;
					fb_x64_imm32(ctx, 0); // placeholder
					fb_x64_record_reloc(ctx, disp_offset, ctx->value_sym[target], -4, FB_RELOC_PLT32);
				} else {
					// Indirect call: reload target to R11, call r11
					i32 target_loc = ctx->value_loc[target];
					i32 offset = (target_loc != FB_LOC_NONE) ? target_loc : fb_x64_spill_offset(ctx, target);
					fb_x64_rex(ctx, true, FB_R11, 0, FB_RBP);
					fb_low_emit_byte(ctx, 0x8B);
					fb_x64_modrm_rbp_disp32(ctx, FB_R11, offset);
					// call r11: REX 41 FF /2 r11
					fb_x64_rex(ctx, false, 0, 0, FB_R11);
					fb_low_emit_byte(ctx, 0xFF);
					fb_x64_modrm(ctx, 0x03, 2, FB_R11);
				}

				// 7. Clean up stack args + padding
				u32 stack_cleanup = stack_arg_count * 8 + stack_padding;
				if (stack_cleanup > 0) {
					fb_x64_rex(ctx, true, 0, 0, FB_RSP);
					if (stack_cleanup <= 127) {
						fb_low_emit_byte(ctx, 0x83);
						fb_x64_modrm(ctx, 0x03, 0, FB_RSP); // /0 = ADD
						fb_x64_imm8(ctx, cast(i8)stack_cleanup);
					} else {
						fb_low_emit_byte(ctx, 0x81);
						fb_x64_modrm(ctx, 0x03, 0, FB_RSP);
						fb_x64_imm32(ctx, cast(i32)stack_cleanup);
					}
				}

				// 8. Capture return value (if non-void, result is in RAX)
				if (inst->r != FB_NOREG) {
					ctx->gp[FB_RAX].vreg     = inst->r;
					ctx->gp[FB_RAX].last_use = ctx->current_inst_idx;
					ctx->gp[FB_RAX].dirty    = true;
					ctx->value_loc[inst->r]  = cast(i32)FB_RAX;
				}
				break;
			}

			case FB_RET: {
				// If returning a value, move it to RAX
				if (inst->a != FB_NOREG) {
					fb_x64_move_value_to_reg(ctx, inst->a, FB_RAX);
				}
				fb_x64_emit_epilogue(ctx);
				break;
			}

			case FB_UNREACHABLE:
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x0B);
				break;

			case FB_TRAP:
			case FB_DEBUGBREAK:
				fb_low_emit_byte(ctx, 0xCC);
				break;

			case FB_UNDEF: {
				// Uninitialized value: just allocate a register, leave it uninitialized
				if (inst->r != FB_NOREG) {
					fb_x64_alloc_gp(ctx, inst->r, 0);
				}
				break;
			}

			case FB_BITCAST: {
				// Reinterpret between same-sized types: just move if needed
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				break;
			}

			case FB_ZEXT: {
				// Zero-extend: source type stored in inst->imm as packed fbType
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fbTypeKind src_tk = cast(fbTypeKind)(inst->imm & 0xFF);

				switch (src_tk) {
				case FBT_I1:
				case FBT_I8:
					// movzx r32, r/m8: 0F B6 modrm (32-bit result zero-extends to 64)
					fb_x64_rex_if_needed(ctx, false, rd, 0, ra);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xB6);
					fb_x64_modrm(ctx, 0x03, rd, ra);
					break;
				case FBT_I16:
					// movzx r32, r/m16: 0F B7 modrm
					fb_x64_rex_if_needed(ctx, false, rd, 0, ra);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xB7);
					fb_x64_modrm(ctx, 0x03, rd, ra);
					break;
				case FBT_I32:
					// mov r32, r32: implicit zero-extend to 64 (clears upper 32 bits)
					fb_x64_rex_if_needed(ctx, false, rd, 0, ra);
					fb_low_emit_byte(ctx, 0x8B);
					fb_x64_modrm(ctx, 0x03, rd, ra);
					break;
				default:
					// Already 64-bit or ptr, no-op (just move if needed)
					if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
					break;
				}
				break;
			}

			case FB_SEXT: {
				// Sign-extend: source type stored in inst->imm as packed fbType
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fbTypeKind src_tk = cast(fbTypeKind)(inst->imm & 0xFF);

				switch (src_tk) {
				case FBT_I1:
				case FBT_I8:
					// movsx r64, r/m8: REX.W 0F BE modrm
					fb_x64_rex(ctx, true, rd, 0, ra);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xBE);
					fb_x64_modrm(ctx, 0x03, rd, ra);
					break;
				case FBT_I16:
					// movsx r64, r/m16: REX.W 0F BF modrm
					fb_x64_rex(ctx, true, rd, 0, ra);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xBF);
					fb_x64_modrm(ctx, 0x03, rd, ra);
					break;
				case FBT_I32:
					// movsxd r64, r/m32: REX.W 63 modrm
					fb_x64_rex(ctx, true, rd, 0, ra);
					fb_low_emit_byte(ctx, 0x63);
					fb_x64_modrm(ctx, 0x03, rd, ra);
					break;
				default:
					// Already 64-bit, no-op
					if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
					break;
				}
				break;
			}

			case FB_TRUNC: {
				// Truncate: no-op at machine level (value is already in register,
				// subsequent ops use the smaller operand size based on their own type)
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				break;
			}

			case FB_PTR2INT:
			case FB_INT2PTR: {
				// On x64, pointers and integers are the same width — trivial mov
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				break;
			}

			// ── Float binary arithmetic ────────────────────────
			// GP→XMM0/1, SSE op, XMM0→GP
			case FB_FADD: fb_x64_float_binop(ctx, inst, 0x58); break;
			case FB_FSUB: fb_x64_float_binop(ctx, inst, 0x5C); break;
			case FB_FMUL: fb_x64_float_binop(ctx, inst, 0x59); break;
			case FB_FDIV: fb_x64_float_binop(ctx, inst, 0x5E); break;
			case FB_FMIN: fb_x64_float_binop(ctx, inst, 0x5D); break;
			case FB_FMAX: fb_x64_float_binop(ctx, inst, 0x5F); break;

			// ── Float unary: FNEG ─────────────────────────────
			case FB_FNEG: {
				fbTypeKind tk = cast(fbTypeKind)(inst->type_raw & 0xFF);
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				if (tk == FBT_F32) {
					// xor r32d, 0x80000000: REX? 81 /6 imm32
					fb_x64_rex_if_needed(ctx, false, 6, 0, rd);
					fb_low_emit_byte(ctx, 0x81);
					fb_x64_modrm(ctx, 0x03, 6, rd);
					fb_x64_imm32(ctx, cast(i32)0x80000000u);
				} else {
					// btc rd, 63: REX.W 0F BA /7 imm8
					fb_x64_rex(ctx, true, 7, 0, rd);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xBA);
					fb_x64_modrm(ctx, 0x03, 7, rd);
					fb_x64_imm8(ctx, 63);
				}
				break;
			}

			// ── Float unary: FABS ─────────────────────────────
			case FB_FABS: {
				fbTypeKind tk = cast(fbTypeKind)(inst->type_raw & 0xFF);
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				if (tk == FBT_F32) {
					// and r32d, 0x7FFFFFFF: REX? 81 /4 imm32
					fb_x64_rex_if_needed(ctx, false, 4, 0, rd);
					fb_low_emit_byte(ctx, 0x81);
					fb_x64_modrm(ctx, 0x03, 4, rd);
					fb_x64_imm32(ctx, 0x7FFFFFFF);
				} else {
					// btr rd, 63: REX.W 0F BA /6 imm8
					fb_x64_rex(ctx, true, 6, 0, rd);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xBA);
					fb_x64_modrm(ctx, 0x03, 6, rd);
					fb_x64_imm8(ctx, 63);
				}
				break;
			}

			// ── Float unary: SQRT ─────────────────────────────
			case FB_SQRT: {
				fbTypeKind tk = cast(fbTypeKind)(inst->type_raw & 0xFF);
				u8 prefix = (tk == FBT_F32) ? 0xF3 : 0xF2;
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fb_x64_gp_to_xmm(ctx, ra, FB_XMM0, tk);
				// sqrtss/sqrtsd xmm0, xmm0: prefix 0F 51 /r
				fb_x64_sse_rr(ctx, prefix, 0x51, FB_XMM0, FB_XMM0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fb_x64_xmm_to_gp(ctx, rd, FB_XMM0, tk);
				break;
			}

			// ── Float comparisons ─────────────────────────────
			// ucomiss/ucomisd sets ZF/PF/CF; NaN sets PF
			case FB_CMP_FEQ: case FB_CMP_FNE:
			case FB_CMP_FLT: case FB_CMP_FLE:
			case FB_CMP_FGT: case FB_CMP_FGE: {
				// Operand type stored in imm by the builder
				fbTypeKind cmp_tk = cast(fbTypeKind)(inst->imm & 0xFF);
				if (cmp_tk != FBT_F32 && cmp_tk != FBT_F64) cmp_tk = FBT_F64;

				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rb = fb_x64_resolve_gp(ctx, inst->b, (1u << ra));

				fb_x64_gp_to_xmm(ctx, ra, FB_XMM0, cmp_tk);
				fb_x64_gp_to_xmm(ctx, rb, FB_XMM1, cmp_tk);

				// ucomiss xmm0, xmm1: [66] 0F 2E /r
				if (cmp_tk == FBT_F64) {
					fb_low_emit_byte(ctx, 0x66); // ucomisd prefix
				}
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x2E);
				fb_x64_modrm(ctx, 0x03, FB_XMM0, FB_XMM1);

				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, cast(u16)((1u << ra) | (1u << rb)));

				// NaN-safe condition code mapping:
				//   FGT → seta (CF=0 && ZF=0) — NaN-safe
				//   FGE → setae (CF=0)         — NaN-safe
				//   FLT → seta with swapped operands, but we already loaded a→xmm0, b→xmm1
				//         so we use setb (CF=1) but that's NaN-unsafe. Instead:
				//         FLT: setb + setnp + AND (ordered and below)
				//   FLE: setbe + setnp + AND
				//   FEQ: sete + setnp + AND (ordered and equal)
				//   FNE: setne + setp + OR  (unordered or not-equal)
				switch (cast(fbOp)inst->op) {
				case FB_CMP_FGT:
					// seta rd
					fb_x64_rex(ctx, false, 0, 0, rd);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0x97);
					fb_x64_modrm(ctx, 0x03, 0, rd);
					break;
				case FB_CMP_FGE:
					// setae rd
					fb_x64_rex(ctx, false, 0, 0, rd);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0x93);
					fb_x64_modrm(ctx, 0x03, 0, rd);
					break;
				case FB_CMP_FEQ:  // sete + setnp + AND
					fb_x64_float_cmp_nan_safe(ctx, rd, 0x94, 0x9B, 0x20, cast(u16)((1u << ra) | (1u << rb)));
					break;
				case FB_CMP_FNE:  // setne + setp + OR
					fb_x64_float_cmp_nan_safe(ctx, rd, 0x95, 0x9A, 0x08, cast(u16)((1u << ra) | (1u << rb)));
					break;
				case FB_CMP_FLT:  // setb + setnp + AND
					fb_x64_float_cmp_nan_safe(ctx, rd, 0x92, 0x9B, 0x20, cast(u16)((1u << ra) | (1u << rb)));
					break;
				case FB_CMP_FLE:  // setbe + setnp + AND
					fb_x64_float_cmp_nan_safe(ctx, rd, 0x96, 0x9B, 0x20, cast(u16)((1u << ra) | (1u << rb)));
					break;
				default: GB_PANIC("unreachable"); break;
				}

				// MOVZX r32, r8: zero-extend byte result to full register
				fb_x64_rex(ctx, false, rd, 0, rd);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0xB6);
				fb_x64_modrm(ctx, 0x03, rd, rd);
				break;
			}

			// ── Float conversions ─────────────────────────────
			case FB_SI2FP: {
				// Signed integer → float: cvtsi2ss/cvtsi2sd
				fbTypeKind dst_tk = cast(fbTypeKind)(inst->type_raw & 0xFF);
				fbTypeKind src_tk = cast(fbTypeKind)(inst->imm & 0xFF);
				u8 prefix = (dst_tk == FBT_F32) ? 0xF3 : 0xF2;
				bool src_64 = (src_tk == FBT_I64 || src_tk == FBT_PTR);

				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg conv_reg = ra;

				// Sub-i32 sources need sign-extension before cvtsi2ss/sd.
				// LOAD uses movzx for i8/i16, so e.g. i8(-1) sits in the GP
				// register as 0xFF = 255. cvtsi2ss r32 reads 32 bits as signed
				// i32, producing 255.0 instead of -1.0 without correction.
				if (src_tk == FBT_I8 || src_tk == FBT_I1) {
					conv_reg = fb_x64_alloc_gp(ctx, FB_NOREG, (1u << ra));
					// movsx r32, r8: REX 0F BE /r (mandatory REX for byte registers)
					fb_x64_rex(ctx, false, conv_reg, 0, ra);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xBE);
					fb_x64_modrm(ctx, 0x03, conv_reg, ra);
				} else if (src_tk == FBT_I16) {
					conv_reg = fb_x64_alloc_gp(ctx, FB_NOREG, (1u << ra));
					// movsx r32, r16: 0F BF /r
					fb_x64_rex_if_needed(ctx, false, conv_reg, 0, ra);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0xBF);
					fb_x64_modrm(ctx, 0x03, conv_reg, ra);
				}

				// cvtsi2ss/sd xmm0, conv_reg: prefix [REX.W] 0F 2A /r
				fb_low_emit_byte(ctx, prefix);
				if (src_64) {
					fb_x64_rex(ctx, true, FB_XMM0, 0, conv_reg);
				} else {
					fb_x64_rex_if_needed(ctx, false, FB_XMM0, 0, conv_reg);
				}
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x2A);
				fb_x64_modrm(ctx, 0x03, FB_XMM0, conv_reg);

				if (conv_reg != ra) {
					ctx->gp[conv_reg].vreg = FB_NOREG;
				}

				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fb_x64_xmm_to_gp(ctx, rd, FB_XMM0, dst_tk);
				break;
			}

			case FB_UI2FP: {
				// Unsigned integer → float
				fbTypeKind dst_tk = cast(fbTypeKind)(inst->type_raw & 0xFF);
				fbTypeKind src_tk = cast(fbTypeKind)(inst->imm & 0xFF);
				u8 prefix = (dst_tk == FBT_F32) ? 0xF3 : 0xF2;
				bool src_u64 = (src_tk == FBT_I64 || src_tk == FBT_PTR);

				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);

				if (!src_u64) {
					// Source fits in signed i64: zero-extend to 64 bits, then cvtsi2ss/sd with REX.W
					// mov r32, r32 to zero-extend (if not already guaranteed)
					fbX64Reg tmp = fb_x64_alloc_gp(ctx, FB_NOREG, (1u << ra));
					fb_x64_rex_if_needed(ctx, false, tmp, 0, ra);
					fb_low_emit_byte(ctx, 0x8B);
					fb_x64_modrm(ctx, 0x03, tmp, ra);
					// cvtsi2ss/sd xmm0, tmp (REX.W)
					fb_low_emit_byte(ctx, prefix);
					fb_x64_rex(ctx, true, FB_XMM0, 0, tmp);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0x2A);
					fb_x64_modrm(ctx, 0x03, FB_XMM0, tmp);
					ctx->gp[tmp].vreg = FB_NOREG;
				} else {
					// Full u64 range: test ra, ra; if negative, use halving trick
					// For simplicity at -O0: use the same signed cvtsi2ss/sd with REX.W
					// This is correct for values < 2^63; for values >= 2^63, it's a known
					// limitation matching the plan's TODO note.
					fb_low_emit_byte(ctx, prefix);
					fb_x64_rex(ctx, true, FB_XMM0, 0, ra);
					fb_low_emit_byte(ctx, 0x0F);
					fb_low_emit_byte(ctx, 0x2A);
					fb_x64_modrm(ctx, 0x03, FB_XMM0, ra);
				}

				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fb_x64_xmm_to_gp(ctx, rd, FB_XMM0, dst_tk);
				break;
			}

			case FB_FP2SI: {
				// Float → signed integer: cvttss2si/cvttsd2si
				fbTypeKind dst_tk = cast(fbTypeKind)(inst->type_raw & 0xFF);
				fbTypeKind src_tk = cast(fbTypeKind)(inst->imm & 0xFF);
				u8 prefix = (src_tk == FBT_F32) ? 0xF3 : 0xF2;
				bool dst_64 = (dst_tk == FBT_I64 || dst_tk == FBT_PTR);

				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fb_x64_gp_to_xmm(ctx, ra, FB_XMM0, src_tk);

				// cvttss2si/cvttsd2si rd, xmm0: prefix [REX.W] 0F 2C /r
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fb_low_emit_byte(ctx, prefix);
				if (dst_64) {
					fb_x64_rex(ctx, true, rd, 0, FB_XMM0);
				} else {
					fb_x64_rex_if_needed(ctx, false, rd, 0, FB_XMM0);
				}
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x2C);
				fb_x64_modrm(ctx, 0x03, rd, FB_XMM0);
				break;
			}

			case FB_FP2UI: {
				// Float → unsigned integer: use signed cvttss2si/cvttsd2si with REX.W
				// Correct for values < 2^63; full u64 range is a known limitation.
				fbTypeKind dst_tk = cast(fbTypeKind)(inst->type_raw & 0xFF);
				fbTypeKind src_tk = cast(fbTypeKind)(inst->imm & 0xFF);
				u8 prefix = (src_tk == FBT_F32) ? 0xF3 : 0xF2;

				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fb_x64_gp_to_xmm(ctx, ra, FB_XMM0, src_tk);

				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fb_low_emit_byte(ctx, prefix);
				fb_x64_rex(ctx, true, rd, 0, FB_XMM0);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x2C);
				fb_x64_modrm(ctx, 0x03, rd, FB_XMM0);
				break;
			}

			case FB_FPEXT: {
				// F32 → F64: cvtss2sd
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fb_x64_movd_gp_to_xmm(ctx, FB_XMM0, ra);
				// cvtss2sd xmm0, xmm0: F3 0F 5A /r
				fb_x64_sse_rr(ctx, 0xF3, 0x5A, FB_XMM0, FB_XMM0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fb_x64_movq_xmm_to_gp(ctx, rd, FB_XMM0);
				break;
			}

			case FB_FPTRUNC: {
				// F64 → F32: cvtsd2ss
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fb_x64_movq_gp_to_xmm(ctx, FB_XMM0, ra);
				// cvtsd2ss xmm0, xmm0: F2 0F 5A /r
				fb_x64_sse_rr(ctx, 0xF2, 0x5A, FB_XMM0, FB_XMM0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				fb_x64_movd_xmm_to_gp(ctx, rd, FB_XMM0);
				break;
			}

			// ── Atomics (Phase 8) ──
			case FB_ATOMIC_LOAD: case FB_ATOMIC_STORE:
			case FB_ATOMIC_XCHG: case FB_ATOMIC_ADD: case FB_ATOMIC_SUB:
			case FB_ATOMIC_AND: case FB_ATOMIC_OR: case FB_ATOMIC_XOR:
			case FB_ATOMIC_CAS: case FB_FENCE:
				GB_PANIC("fast backend: atomic operation not yet lowered (opcode %d)", inst->op);
				break;

			// ── Wide arithmetic ──
			case FB_ADDPAIR: case FB_MULPAIR:
				GB_PANIC("fast backend: wide arithmetic not yet lowered (opcode %d)", inst->op);
				break;

			// ── Bit manipulation ──────────────────────────────
			case FB_BSWAP: {
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				if (rd != ra) fb_x64_mov_rr(ctx, rd, ra);
				// bswap rd: REX.W 0F C8+rd
				fb_x64_rex(ctx, true, 0, 0, rd);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, cast(u8)(0xC8 + (rd & 7)));
				break;
			}

			case FB_POPCNT: {
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				// popcnt rd, ra: F3 REX.W 0F B8 /r
				fb_low_emit_byte(ctx, 0xF3);
				fb_x64_rex(ctx, true, rd, 0, ra);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0xB8);
				fb_x64_modrm(ctx, 0x03, rd, ra);
				break;
			}

			case FB_CLZ: {
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				// lzcnt rd, ra: F3 REX.W 0F BD /r
				fb_low_emit_byte(ctx, 0xF3);
				fb_x64_rex(ctx, true, rd, 0, ra);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0xBD);
				fb_x64_modrm(ctx, 0x03, rd, ra);
				break;
			}

			case FB_CTZ: {
				fbX64Reg ra = fb_x64_resolve_gp(ctx, inst->a, 0);
				fbX64Reg rd = fb_x64_alloc_gp(ctx, inst->r, (1u << ra));
				// tzcnt rd, ra: F3 REX.W 0F BC /r
				fb_low_emit_byte(ctx, 0xF3);
				fb_x64_rex(ctx, true, rd, 0, ra);
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0xBC);
				fb_x64_modrm(ctx, 0x03, rd, ra);
				break;
			}

			// ── SIMD (Phase 8) ──
			case FB_VSHUFFLE: case FB_VEXTRACT: case FB_VINSERT: case FB_VSPLAT:
				GB_PANIC("fast backend: SIMD operation not yet lowered (opcode %d)", inst->op);
				break;

			// ── Miscellaneous ──
			case FB_MEMSET: case FB_VA_START: case FB_PREFETCH:
			case FB_CYCLE: case FB_ASM: case FB_PHI:
			case FB_TAILCALL:
				GB_PANIC("fast backend: operation not yet lowered (opcode %d)", inst->op);
				break;

			default:
				GB_PANIC("fast backend: unknown opcode %d", inst->op);
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

		// Copy relocations from lowering context to proc
		p->reloc_count = ctx.reloc_count;
		p->reloc_cap   = ctx.reloc_count;
		if (ctx.reloc_count > 0) {
			p->relocs = gb_alloc_array(heap_allocator(), fbReloc, ctx.reloc_count);
			gb_memmove(p->relocs, ctx.relocs, sizeof(fbReloc) * ctx.reloc_count);
		}

		if (ctx.code)           gb_free(heap_allocator(), ctx.code);
		if (ctx.block_offsets)  gb_free(heap_allocator(), ctx.block_offsets);
		if (ctx.value_loc)      gb_free(heap_allocator(), ctx.value_loc);
		if (ctx.value_sym)      gb_free(heap_allocator(), ctx.value_sym);
		if (ctx.fixups)         gb_free(heap_allocator(), ctx.fixups);
		if (ctx.relocs)         gb_free(heap_allocator(), ctx.relocs);
	}
}
