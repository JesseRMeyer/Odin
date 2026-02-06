// Fast Backend — entity iteration, procedure IR generation
//
// Phase 2: every non-foreign procedure gets a void-return stub (push rbp / mov rbp,rsp /
// pop rbp / ret). Return values are not yet populated, so RAX is nondeterministic.
// This exists purely for pipeline validation (parse → check → IR → lower → emit → link).
// Full procedure body lowering begins in Phase 4+.

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
			u32 entry = fb_block_create(p);
			fb_block_start(p, entry);
			fb_inst_emit(p, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		}

		array_add(&m->procs, p);
	}
}
