// Fast Backend — entity iteration, procedure IR generation
//
// Phase 4: every non-foreign procedure gets a test IR sequence that exercises
// multi-block control flow (ICONST, CMP_EQ, BRANCH, JUMP, RET).
// Full procedure body lowering from AST begins in Phase 6+.

gb_internal void fb_generate_procedures(fbModule *m) {
	CheckerInfo *info = m->info;

	for (Entity *e : info->entities) {
		Scope *scope = e->scope;

		if ((scope->flags & ScopeFlag_File) == 0) {
			continue;
		}
		if (e->kind != Entity_Procedure) {
			continue;
		}
		if (e->min_dep_count.load(std::memory_order_relaxed) == 0) {
			continue;
		}

		fbProc *p = fb_proc_create(m, e);

		// Entry point needs global linkage
		if (e == info->entry_point) {
			p->is_export = true;
		}
		// Respect linkage="strong" — these procs need global visibility
		// (e.g., runtime.main has @(linkage="strong") to be visible to CRT)
		if (e->flags & EntityFlag_CustomLinkage_Strong) {
			p->is_export = true;
		}

		if (!p->is_foreign) {
			// Phase 4 test IR: multi-block control flow
			// Block 0: ICONST 42 → ICONST 0 → CMP_EQ → BRANCH(cond, block1, block2)
			// Block 1: ICONST 1 → JUMP block2
			// Block 2: RET
			u32 block0 = fb_block_create(p);
			u32 block1 = fb_block_create(p);
			u32 block2 = fb_block_create(p);

			fb_block_start(p, block0);
			u32 const42 = fb_inst_emit(p, FB_ICONST, FB_I64, FB_NOREG, FB_NOREG, FB_NOREG, 0, 42);
			u32 const0  = fb_inst_emit(p, FB_ICONST, FB_I64, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
			u32 cmp     = fb_inst_emit(p, FB_CMP_EQ, FB_I1, const42, const0, FB_NOREG, 0, 0);
			fb_inst_emit(p, FB_BRANCH, FB_VOID, cmp, block1, block2, 0, 0);

			fb_block_start(p, block1);
			u32 const1 = fb_inst_emit(p, FB_ICONST, FB_I64, FB_NOREG, FB_NOREG, FB_NOREG, 0, 1);
			gb_unused(const1);
			fb_inst_emit(p, FB_JUMP, FB_VOID, block2, FB_NOREG, FB_NOREG, 0, 0);

			fb_block_start(p, block2);
			fb_inst_emit(p, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		}

		array_add(&m->procs, p);
	}

	// Generate __$startup_runtime and __$cleanup_runtime stubs.
	// The runtime declares these as foreign (signatures only), but every backend
	// must synthesize implementations. For Phase 2 the bodies are just `ret`.
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (!p->is_foreign) continue;

		bool is_startup = str_eq(p->name, str_lit("__$startup_runtime"));
		bool is_cleanup = str_eq(p->name, str_lit("__$cleanup_runtime"));
		if (!is_startup && !is_cleanup) continue;

		// Convert from foreign declaration to defined stub with global visibility
		p->is_foreign = false;
		p->is_export  = true;

		p->inst_cap  = 8;
		p->insts     = gb_alloc_array(heap_allocator(), fbInst, p->inst_cap);
		p->block_cap = 2;
		p->blocks    = gb_alloc_array(heap_allocator(), fbBlock, p->block_cap);
		p->slot_cap  = 1;
		p->slots     = gb_alloc_array(heap_allocator(), fbStackSlot, p->slot_cap);
		p->aux_cap   = 4;
		p->aux       = gb_alloc_array(heap_allocator(), u32, p->aux_cap);
		p->loc_cap   = 2;
		p->locs      = gb_alloc_array(heap_allocator(), fbLoc, p->loc_cap);

		u32 entry = fb_block_create(p);
		fb_block_start(p, entry);
		fb_inst_emit(p, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
	}
}
