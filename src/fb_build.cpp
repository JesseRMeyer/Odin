// Fast Backend — entity iteration, procedure IR generation
//
// Phase 5: prologue-based parameter receiving. Every non-foreign procedure gets
// parameter stack slots via fb_setup_params(), then test IR that exercises
// parameter flow (ALLOCA + LOAD param, ADD 1, RET) or function calls.

// ───────────────────────────────────────────────────────────────────────
// Parameter setup: classify params via ABI, create stack slots, record param_locs
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_setup_params(fbProc *p) {
	Type *pt = base_type(p->odin_type);
	GB_ASSERT(pt != nullptr && pt->kind == Type_Proc);

	TypeProc *proc_type = &pt->Proc;
	if (proc_type->params == nullptr && proc_type->calling_convention != ProcCC_Odin) {
		return;
	}

	i32 param_count = proc_type->param_count;
	bool has_context = (proc_type->calling_convention == ProcCC_Odin);

	// Count how many GP register slots we need
	u32 gp_idx = 0;
	u32 max_gp_params = param_count + (has_context ? 1 : 0);
	if (max_gp_params == 0) return;

	// Temporary: allocate for the hard upper bound on GP register params
	u32 *locs = gb_alloc_array(heap_allocator(), u32, FB_X64_SYSV_MAX_GP_ARGS);

	// Process declared parameters
	TypeTuple *params = proc_type->params ? &proc_type->params->Tuple : nullptr;
	for (i32 i = 0; i < param_count && params != nullptr; i++) {
		Entity *e = params->variables[i];
		if (e == nullptr || e->kind != Entity_Variable) continue;

		Type *param_type = e->type;
		fbABIParamInfo abi = fb_abi_classify_type_sysv(param_type);

		if (abi.num_classes == 0 || abi.classes[0] == FB_ABI_IGNORE) {
			continue;
		}

		if (abi.classes[0] == FB_ABI_MEMORY) {
			// MEMORY class: passed on stack by caller, handled in Phase 6+
			continue;
		}

		if (abi.classes[0] == FB_ABI_SSE) {
			// SSE params: Phase 8
			continue;
		}

		// INTEGER class: each eightbyte consumes one GP register.
		// Param slots are always register-width (8 bytes, 8-aligned).
		// The SysV ABI says upper bits of narrow params are undefined,
		// so we store the full register and let the IR type system govern load width.
		for (u8 ci = 0; ci < abi.num_classes; ci++) {
			if (abi.classes[ci] != FB_ABI_INTEGER) continue;
			if (gp_idx >= FB_X64_SYSV_MAX_GP_ARGS) break; // overflow to stack

			u32 slot = fb_slot_create(p, 8, 8, e, param_type);
			locs[gp_idx++] = slot;
		}
	}

	// Odin CC: append context pointer as the last GP parameter
	if (has_context && gp_idx < FB_X64_SYSV_MAX_GP_ARGS) {
		u32 slot = fb_slot_create(p, 8, 8, nullptr, nullptr);
		locs[gp_idx++] = slot;
	}

	if (gp_idx > 0) {
		p->param_locs  = locs;
		p->param_count = gp_idx;
	} else {
		gb_free(heap_allocator(), locs);
	}
}

// ───────────────────────────────────────────────────────────────────────
// Procedure generation
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_generate_procedures(fbModule *m) {
	CheckerInfo *info = m->info;

	// First pass: create all procedure objects (including foreign declarations)
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

		array_add(&m->procs, p);
	}

	// Generate __$startup_runtime and __$cleanup_runtime stubs.
	// The runtime declares these as foreign (signatures only), but every backend
	// must synthesize implementations. The bodies are just `ret` for now.
	// This must happen before the test IR loop so we can find their proc indices.
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

	// Find __$startup_runtime proc index for SYMADDR test
	u32 startup_proc_idx = FB_NOREG;
	for_array(i, m->procs) {
		if (str_eq(m->procs[i]->name, str_lit("__$startup_runtime"))) {
			startup_proc_idx = cast(u32)i;
			break;
		}
	}

	// Second pass: emit test IR for non-foreign, non-stub procedures
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign) continue;
		if (p->inst_count > 0) continue; // skip stubs already populated

		// Set up parameter receiving for all non-foreign procs
		fb_setup_params(p);

		u32 bb0 = fb_block_create(p);
		fb_block_start(p, bb0);

		bool is_entry = (p->entity == info->entry_point);

		if (is_entry && startup_proc_idx != FB_NOREG) {
			// Entry point: SYMADDR + CALL startup_runtime + RET 0
			u32 sym = fb_inst_emit(p, FB_SYMADDR, FB_PTR, FB_NOREG, FB_NOREG, FB_NOREG, 0, cast(i64)startup_proc_idx);
			fb_inst_emit(p, FB_CALL, FB_VOID, sym, p->aux_count, 0, 0, 0);
			u32 zero = fb_inst_emit(p, FB_ICONST, FB_I64, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
			fb_inst_emit(p, FB_RET, FB_VOID, zero, FB_NOREG, FB_NOREG, 0, 0);
		} else if (p->param_count > 0) {
			// Procs with params: ALLOCA first param slot → LOAD → ADD 1 → RET
			// This proves parameter flow: ABI reg → prologue store → stack → LOAD → computation → return
			u32 slot_idx = p->param_locs[0];
			fbStackSlot *slot = &p->slots[slot_idx];

			// Determine the scalar type for the loaded value
			fbType load_type = FB_I64; // default
			if (slot->odin_type != nullptr) {
				fbType dt = fb_data_type(slot->odin_type);
				if (dt.kind != FBT_VOID) {
					load_type = dt;
				}
			}

			u32 ptr = fb_inst_emit(p, FB_ALLOCA, FB_PTR, slot_idx, FB_NOREG, FB_NOREG, 0, 0);
			u32 val = fb_inst_emit(p, FB_LOAD, load_type, ptr, FB_NOREG, FB_NOREG, 0, 0);
			u32 one = fb_inst_emit(p, FB_ICONST, load_type, FB_NOREG, FB_NOREG, FB_NOREG, 0, 1);
			u32 sum = fb_inst_emit(p, FB_ADD, load_type, val, one, FB_NOREG, 0, 0);
			fb_inst_emit(p, FB_RET, FB_VOID, sum, FB_NOREG, FB_NOREG, 0, 0);
		} else {
			// Procs without params: RET void
			fb_inst_emit(p, FB_RET, FB_VOID, FB_NOREG, FB_NOREG, FB_NOREG, 0, 0);
		}
	}
}
