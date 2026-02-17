// Fast Backend Verification — structural passes
//
// fb_verify_proc:     per-procedure IR integrity (after build, before lowering)
//                     Uses GB_ASSERT_MSG — recoverable during generation so procs
//                     with invalid IR get stubbed rather than crashing the compiler.
// fb_verify_module:   module-level post-lowering checks (before ELF emission)
//                     Uses FB_VERIFY — hard crash, these are always compiler bugs.
// fb_verify_regalloc: register allocator bidirectional consistency (during lowering)
//                     Uses FB_VERIFY — hard crash, always compiler bugs.

// ───────────────────────────────────────────────────────────────────────
// Helper: validate a single operand against its spec role
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_verify_operand(fbProc *p, u32 inst_idx, fbInst *inst,
                                    const char *slot_name, u32 val, fbOperandRole role) {
	const char *op_name = (inst->op < FB_OP_COUNT) ? fb_op_names[inst->op] : "???";
	switch (role) {
	case FBO_NONE:
		GB_ASSERT_MSG(val == FB_NOREG,
			"FB_VERIFY: proc='%.*s', inst=%u, op=%s, %s=%u must be FB_NOREG",
			LIT(p->name), inst_idx, op_name, slot_name, val);
		break;
	case FBO_VALUE:
		GB_ASSERT_MSG(val < p->next_value,
			"FB_VERIFY: proc='%.*s', inst=%u, op=%s, %s=%u >= next_value=%u",
			LIT(p->name), inst_idx, op_name, slot_name, val, p->next_value);
		break;
	case FBO_VALUE_OPT:
		GB_ASSERT_MSG(val < p->next_value || val == FB_NOREG,
			"FB_VERIFY: proc='%.*s', inst=%u, op=%s, %s=%u invalid (next_value=%u)",
			LIT(p->name), inst_idx, op_name, slot_name, val, p->next_value);
		break;
	case FBO_BLOCK:
		GB_ASSERT_MSG(val < p->block_count,
			"FB_VERIFY: proc='%.*s', inst=%u, op=%s, %s=%u >= block_count=%u",
			LIT(p->name), inst_idx, op_name, slot_name, val, p->block_count);
		break;
	case FBO_SLOT:
		GB_ASSERT_MSG(val < p->slot_count,
			"FB_VERIFY: proc='%.*s', inst=%u, op=%s, %s=%u >= slot_count=%u",
			LIT(p->name), inst_idx, op_name, slot_name, val, p->slot_count);
		break;
	case FBO_AUX:
		GB_ASSERT_MSG(val < p->aux_count,
			"FB_VERIFY: proc='%.*s', inst=%u, op=%s, %s=%u >= aux_count=%u",
			LIT(p->name), inst_idx, op_name, slot_name, val, p->aux_count);
		break;
	case FBO_COUNT:
		// Raw count — no range constraint
		break;
	}
}

// ───────────────────────────────────────────────────────────────────────
// fb_verify_proc — full IR sweep after construction, before lowering
//
// Uses GB_ASSERT_MSG (recoverable) because this runs inside the recovery
// scope. Invalid IR causes the proc to be stubbed, not the compiler to crash.
// This is appropriate during development while many features are unimplemented.
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_verify_proc(fbProc *p) {
	if (p->is_foreign) return;
	if (p->inst_count == 0 && p->block_count == 0) return; // stub

	// 1. Block validity: all blocks must have been started (first_inst != sentinel)
	for (u32 i = 0; i < p->block_count; i++) {
		GB_ASSERT_MSG(p->blocks[i].first_inst != UINT32_MAX,
			"FB_VERIFY: proc='%.*s', block %u was never started (first_inst=UINT32_MAX)",
			LIT(p->name), i);
	}

	// 2. Block contiguity: blocks sorted by first_inst must tile the instruction array.
	//    Blocks are created eagerly for branch targets but filled in control-flow order,
	//    so block IDs are NOT in instruction order. Sort a copy of indices by first_inst.
	{
		u32 *sorted = gb_alloc_array(heap_allocator(), u32, p->block_count);
		for (u32 i = 0; i < p->block_count; i++) sorted[i] = i;
		// Insertion sort (block_count is small, typically < 100)
		for (u32 i = 1; i < p->block_count; i++) {
			u32 key = sorted[i];
			u32 key_fi = p->blocks[key].first_inst;
			i32 j = cast(i32)i - 1;
			while (j >= 0 && p->blocks[sorted[j]].first_inst > key_fi) {
				sorted[j + 1] = sorted[j];
				j--;
			}
			sorted[j + 1] = key;
		}
		for (u32 i = 0; i + 1 < p->block_count; i++) {
			u32 bi = sorted[i];
			u32 bj = sorted[i + 1];
			u32 end = p->blocks[bi].first_inst + p->blocks[bi].inst_count;
			GB_ASSERT_MSG(end == p->blocks[bj].first_inst,
				"FB_VERIFY: proc='%.*s', sorted block %u (id=%u) ends at inst %u but block %u (id=%u) starts at %u",
				LIT(p->name), i, bi, end, i + 1, bj, p->blocks[bj].first_inst);
		}
		gb_free(heap_allocator(), sorted);
	}

	// 3. Total coverage: sum of all block inst_counts == total inst_count
	{
		u32 total = 0;
		for (u32 i = 0; i < p->block_count; i++) {
			total += p->blocks[i].inst_count;
		}
		GB_ASSERT_MSG(total == p->inst_count,
			"FB_VERIFY: proc='%.*s', block inst sum=%u != inst_count=%u",
			LIT(p->name), total, p->inst_count);
	}

	// 4. SSA single-definition bitmap
	u8 *defined = gb_alloc_array(heap_allocator(), u8, (p->next_value + 7) / 8);
	gb_zero_size(defined, (p->next_value + 7) / 8);

	// 5. Per-instruction validation
	for (u32 bi = 0; bi < p->block_count; bi++) {
		fbBlock *blk = &p->blocks[bi];

		for (u32 ii = 0; ii < blk->inst_count; ii++) {
			u32 inst_idx = blk->first_inst + ii;
			GB_ASSERT_MSG(inst_idx < p->inst_count,
				"FB_VERIFY: proc='%.*s', block %u references inst %u >= inst_count=%u",
				LIT(p->name), bi, inst_idx, p->inst_count);

			fbInst *inst = &p->insts[inst_idx];
			fbOp op = cast(fbOp)inst->op;

			// Valid opcode
			GB_ASSERT_MSG(op < FB_OP_COUNT,
				"FB_VERIFY: proc='%.*s', inst=%u, invalid opcode %u",
				LIT(p->name), inst_idx, (u32)op);

			// Valid type
			fbType ft = fb_type_unpack(inst->type_raw);
			GB_ASSERT_MSG(ft.kind < FBT_COUNT,
				"FB_VERIFY: proc='%.*s', inst=%u, op=%s, invalid type kind %u",
				LIT(p->name), inst_idx, fb_op_names[op], (u32)ft.kind);

			const fbOpSpec *spec = &fb_op_specs[op];

			// Operand validation
			fb_verify_operand(p, inst_idx, inst, "a", inst->a, spec->a);
			fb_verify_operand(p, inst_idx, inst, "b", inst->b, spec->b);
			fb_verify_operand(p, inst_idx, inst, "c", inst->c, spec->c);

			// Result consistency: has_result && type != VOID ↔ r != FB_NOREG
			// Note: CALL with void return has has_result=true but type=VOID → r=FB_NOREG is correct
			if (spec->has_result && ft.kind != FBT_VOID) {
				GB_ASSERT_MSG(inst->r != FB_NOREG,
					"FB_VERIFY: proc='%.*s', inst=%u, op=%s has result but r=FB_NOREG",
					LIT(p->name), inst_idx, fb_op_names[op]);
			}
			if (!spec->has_result) {
				GB_ASSERT_MSG(inst->r == FB_NOREG,
					"FB_VERIFY: proc='%.*s', inst=%u, op=%s has no result but r=%u",
					LIT(p->name), inst_idx, fb_op_names[op], inst->r);
			}

			// SSA single-definition
			if (inst->r != FB_NOREG) {
				GB_ASSERT_MSG(inst->r < p->next_value,
					"FB_VERIFY: proc='%.*s', inst=%u, op=%s, r=%u >= next_value=%u",
					LIT(p->name), inst_idx, fb_op_names[op], inst->r, p->next_value);
				u32 byte = inst->r / 8;
				u8  bit  = 1 << (inst->r % 8);
				GB_ASSERT_MSG(!(defined[byte] & bit),
					"FB_VERIFY: proc='%.*s', inst=%u, op=%s, value %u defined more than once",
					LIT(p->name), inst_idx, fb_op_names[op], inst->r);
				defined[byte] |= bit;
			}

			// Block termination: last instruction must be a terminator.
			// Mid-block terminators (e.g., TRAP followed by dead code) are allowed
			// because the builder emits linearly without always pruning dead code.
			bool is_last = (ii == blk->inst_count - 1);
			if (is_last && !spec->is_terminator) {
				GB_ASSERT_MSG(false,
					"FB_VERIFY: proc='%.*s', block %u not terminated (last op=%s at inst=%u)",
					LIT(p->name), bi, fb_op_names[op], inst_idx);
			}

			// CALL aux bounds: aux[b..b+c) must be in range, each entry < next_value
			if (op == FB_CALL || op == FB_TAILCALL) {
				u32 aux_start = inst->b;
				u32 arg_count = inst->c;
				if (arg_count > 0) {
					GB_ASSERT_MSG(aux_start + arg_count <= p->aux_count,
						"FB_VERIFY: proc='%.*s', inst=%u, op=%s, aux[%u..%u) out of range (aux_count=%u)",
						LIT(p->name), inst_idx, fb_op_names[op],
						aux_start, aux_start + arg_count, p->aux_count);
					for (u32 ai = 0; ai < arg_count; ai++) {
						u32 arg_val = p->aux[aux_start + ai];
						GB_ASSERT_MSG(arg_val < p->next_value,
							"FB_VERIFY: proc='%.*s', inst=%u, op=%s, aux[%u]=%u >= next_value=%u",
							LIT(p->name), inst_idx, fb_op_names[op],
							aux_start + ai, arg_val, p->next_value);
					}
				}
			}

			// SWITCH aux bounds: aux[c..c+imm*2) in range; odd entries (blocks) < block_count
			if (op == FB_SWITCH) {
				u32 aux_start = inst->c;
				u32 case_count = cast(u32)inst->imm;
				if (case_count > 0) {
					GB_ASSERT_MSG(aux_start + case_count * 2 <= p->aux_count,
						"FB_VERIFY: proc='%.*s', inst=%u, SWITCH aux[%u..%u) out of range (aux_count=%u)",
						LIT(p->name), inst_idx,
						aux_start, aux_start + case_count * 2, p->aux_count);
					for (u32 ci = 0; ci < case_count; ci++) {
						u32 case_block = p->aux[aux_start + ci * 2 + 1];
						GB_ASSERT_MSG(case_block < p->block_count,
							"FB_VERIFY: proc='%.*s', inst=%u, SWITCH case %u block=%u >= block_count=%u",
							LIT(p->name), inst_idx, ci, case_block, p->block_count);
					}
				}
			}
		}
	}

	gb_free(heap_allocator(), defined);
}

// ───────────────────────────────────────────────────────────────────────
// fb_verify_module — post-lowering, pre-ELF emission
//
// Uses FB_VERIFY — hard crash. At this point all procs should be valid
// (either properly generated or stubbed). Any failure here is a compiler bug.
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_verify_module(fbModule *m) {
	u32 proc_count  = cast(u32)m->procs.count;
	u32 rodata_count = cast(u32)m->rodata_entries.count;
	u32 global_count = cast(u32)m->global_entries.count;

	for_array(pi, m->procs) {
		fbProc *p = m->procs[pi];
		if (p->is_foreign) continue;

		// Every non-foreign proc must have machine code after lowering
		// (stubs have inst_count==0, block_count==0 — they still get an empty prologue+epilogue)
		FB_VERIFY_MSG(p->machine_code != nullptr,
			"proc='%.*s' has no machine code after lowering",
			LIT(p->name));
		FB_VERIFY_MSG(p->machine_code_size > 0,
			"proc='%.*s' has zero-size machine code after lowering",
			LIT(p->name));

		// Validate all relocations
		for (u32 ri = 0; ri < p->reloc_count; ri++) {
			fbReloc *rel = &p->relocs[ri];
			u32 sym = rel->target_sym;
			bool valid_proc   = sym < proc_count;
			bool valid_rodata = sym >= FB_RODATA_SYM_BASE && (sym - FB_RODATA_SYM_BASE) < rodata_count;
			bool valid_global = sym >= FB_GLOBAL_SYM_BASE && (sym - FB_GLOBAL_SYM_BASE) < global_count;
			FB_VERIFY_MSG(valid_proc || valid_rodata || valid_global,
				"proc='%.*s', reloc %u has invalid target_sym=0x%x",
				LIT(p->name), ri, sym);
		}
	}

	// Validate data relocations
	for_array(di, m->data_relocs) {
		fbDataReloc *dr = &m->data_relocs[di];
		FB_VERIFY_MSG(dr->global_idx < global_count,
			"data_reloc %u has global_idx=%u >= global_count=%u",
			(u32)di, dr->global_idx, global_count);

		u32 sym = dr->target_sym;
		bool valid_proc   = sym < proc_count;
		bool valid_rodata = sym >= FB_RODATA_SYM_BASE && (sym - FB_RODATA_SYM_BASE) < rodata_count;
		bool valid_global = sym >= FB_GLOBAL_SYM_BASE && (sym - FB_GLOBAL_SYM_BASE) < global_count;
		FB_VERIFY_MSG(valid_proc || valid_rodata || valid_global,
			"data_reloc %u has invalid target_sym=0x%x",
			(u32)di, sym);
	}

	// Entry point indices
	if (m->startup_proc_idx != FB_NOREG) {
		FB_VERIFY_MSG(m->startup_proc_idx < proc_count,
			"startup_proc_idx=%u >= proc_count=%u",
			m->startup_proc_idx, proc_count);
	}
	if (m->entry_proc_idx != FB_NOREG) {
		FB_VERIFY_MSG(m->entry_proc_idx < proc_count,
			"entry_proc_idx=%u >= proc_count=%u",
			m->entry_proc_idx, proc_count);
	}
}

// ───────────────────────────────────────────────────────────────────────
// fb_verify_regalloc — bidirectional register ↔ value_loc consistency
//
// Uses FB_VERIFY — hard crash. Any inconsistency in the register allocator
// during lowering is always a compiler bug.
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_verify_regalloc(fbLowCtx *ctx) {
	// Forward: for each register with a live value, value_loc must point back
	for (int r = 0; r < 16; r++) {
		u32 vreg = ctx->gp[r].vreg;
		if (vreg == FB_NOREG) continue;
		FB_VERIFY_MSG(vreg < ctx->value_loc_count,
			"regalloc: gp[%d].vreg=%u >= value_loc_count=%u in proc='%.*s'",
			r, vreg, ctx->value_loc_count, LIT(ctx->proc->name));
		FB_VERIFY_MSG(ctx->value_loc[vreg] == cast(i32)r,
			"regalloc: gp[%d].vreg=%u but value_loc[%u]=%d in proc='%.*s'",
			r, vreg, vreg, ctx->value_loc[vreg], LIT(ctx->proc->name));
	}

	// Reverse: for each value in a register, the register must claim it
	for (u32 v = 0; v < ctx->value_loc_count; v++) {
		i32 loc = ctx->value_loc[v];
		if (loc < 0 || loc >= 16) continue;
		FB_VERIFY_MSG(ctx->gp[loc].vreg == v,
			"regalloc: value_loc[%u]=%d but gp[%d].vreg=%u in proc='%.*s'",
			v, loc, loc, ctx->gp[loc].vreg, LIT(ctx->proc->name));
	}
}
