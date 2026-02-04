// llvm_backend_comp.cpp — JIT evaluator for #comp compile-time function evaluation

#include <setjmp.h>
#include <llvm-c/LLJIT.h>
#include <llvm-c/Orc.h>
#include <llvm-c/OrcEE.h>

#include <thread>
#include <chrono>
#include <mutex>
#include <condition_variable>

// Forward declaration — defined later in llvm_backend.cpp
gb_internal void lb_generate_procedure(lbModule *m, lbProcedure *p);

// ---------------------------------------------------------------------------
// LLVM Native Target Initialization (lazy, once)
// ---------------------------------------------------------------------------

gb_global std::once_flag comp_llvm_init_flag;

gb_internal void comp_ensure_llvm_initialized() {
	std::call_once(comp_llvm_init_flag, []() {
		LLVMInitializeNativeTarget();
		LLVMInitializeNativeAsmPrinter();
		LLVMInitializeNativeAsmParser();
	});
}

// ---------------------------------------------------------------------------
// JIT Trap State (thread-local, for runtime error interception)
// ---------------------------------------------------------------------------

struct CompJITTrapState {
	jmp_buf recovery;
	bool    panicked;
	char    panic_msg[512];
};

gb_global thread_local CompJITTrapState comp_trap_state;

// ---------------------------------------------------------------------------
// Runtime Error Stubs
// ---------------------------------------------------------------------------
// These are called by JIT-compiled code when a runtime check fails.
// They capture the error and longjmp back to the evaluator.

extern "C" {

static void comp_stub_bounds_check_error(
	void *file_ptr, i32 file_len,
	i32 line, i32 column,
	i64 index, i64 count
) {
	(void)file_ptr; (void)file_len; (void)line; (void)column;
	gb_snprintf(comp_trap_state.panic_msg, sizeof(comp_trap_state.panic_msg),
		"index out of bounds — index %lld, length %lld",
		(long long)index, (long long)count);
	comp_trap_state.panicked = true;
	longjmp(comp_trap_state.recovery, 1);
}

static void comp_stub_slice_expr_error_hi(
	void *file_ptr, i32 file_len,
	i32 line, i32 column,
	i64 hi, i64 len
) {
	(void)file_ptr; (void)file_len; (void)line; (void)column;
	gb_snprintf(comp_trap_state.panic_msg, sizeof(comp_trap_state.panic_msg),
		"slice high bound out of range — hi %lld, length %lld",
		(long long)hi, (long long)len);
	comp_trap_state.panicked = true;
	longjmp(comp_trap_state.recovery, 1);
}

static void comp_stub_slice_expr_error_lo_hi(
	void *file_ptr, i32 file_len,
	i32 line, i32 column,
	i64 lo, i64 hi
) {
	(void)file_ptr; (void)file_len; (void)line; (void)column;
	gb_snprintf(comp_trap_state.panic_msg, sizeof(comp_trap_state.panic_msg),
		"slice low > high — lo %lld, hi %lld",
		(long long)lo, (long long)hi);
	comp_trap_state.panicked = true;
	longjmp(comp_trap_state.recovery, 1);
}

static void comp_stub_panic(void *msg_ptr, i64 msg_len) {
	i64 copy_len = gb_min(msg_len, (i64)sizeof(comp_trap_state.panic_msg) - 1);
	if (copy_len > 0 && msg_ptr != nullptr) {
		gb_memmove(comp_trap_state.panic_msg, msg_ptr, cast(isize)copy_len);
	}
	comp_trap_state.panic_msg[copy_len] = 0;
	comp_trap_state.panicked = true;
	longjmp(comp_trap_state.recovery, 1);
}

// Generic trap for any unresolved runtime symbol
static void comp_stub_generic_trap() {
	gb_snprintf(comp_trap_state.panic_msg, sizeof(comp_trap_state.panic_msg),
		"runtime error during #comp evaluation");
	comp_trap_state.panicked = true;
	longjmp(comp_trap_state.recovery, 1);
}

} // extern "C"

// CompEvalResult is forward-declared in checker.cpp (which is included
// earlier in the single compilation unit).

// ---------------------------------------------------------------------------
// JIT Module Setup
// ---------------------------------------------------------------------------

// Initialize a minimal lbModule for JIT compilation.
// This mirrors lb_init_module_worker_proc but with only what's needed for
// standalone procedure compilation.
gb_internal void comp_init_jit_module(lbModule *m, Checker *checker) {
	m->checker = checker;
	m->info    = &checker->info;
	// m->gen is set by the caller (comp_evaluate) to point to the enclosing lbGenerator.
	m->pkg     = nullptr;
	m->file    = nullptr;
	m->module_name = "comp_eval";

	m->ctx = LLVMContextCreate();
	m->mod = LLVMModuleCreateWithNameInContext(m->module_name, m->ctx);
	m->debug_builder = nullptr; // No debug info for JIT

	// Set up host target
	char *host_triple = LLVMGetDefaultTargetTriple();
	LLVMSetTarget(m->mod, host_triple);

	LLVMTargetRef host_target = {};
	char *err_msg = nullptr;
	if (LLVMGetTargetFromTriple(host_triple, &host_target, &err_msg)) {
		if (err_msg) LLVMDisposeMessage(err_msg);
		LLVMDisposeMessage(host_triple);
		return;
	}

	m->target_machine = LLVMCreateTargetMachine(
		host_target, host_triple,
		"generic", "",
		LLVMCodeGenLevelDefault,
		LLVMRelocDefault,
		LLVMCodeModelJITDefault
	);

	LLVMSetModuleDataLayout(m->mod, LLVMCreateTargetDataLayout(m->target_machine));
	LLVMDisposeMessage(host_triple);

	// Initialize all maps and data structures
	map_init(&m->types);
	map_init(&m->func_raw_types);
	map_init(&m->struct_field_remapping);
	map_init(&m->values);
	map_init(&m->soa_values);
	string_map_init(&m->members);
	string_map_init(&m->procedures);
	string_map_init(&m->const_strings);
	string16_map_init(&m->const_string16s);
	map_init(&m->function_type_map);
	string_map_init(&m->gen_procs);
	mpsc_init(&m->procedures_to_generate, heap_allocator());
	map_init(&m->procedure_values, 64);
	array_init(&m->generated_procedures, heap_allocator(), 0, 64);
	array_init(&m->global_procedures_to_create, heap_allocator(), 0, 64);
	array_init(&m->global_types_to_create, heap_allocator(), 0, 64);
	mpsc_init(&m->missing_procedures_to_check, heap_allocator());
	map_init(&m->debug_values);
	string_map_init(&m->objc_classes);
	string_map_init(&m->objc_selectors);
	string_map_init(&m->objc_ivars);
	map_init(&m->map_info_map, 0);
	map_init(&m->map_cell_info_map, 0);
	map_init(&m->exact_value_compound_literal_addr_map, 64);
	array_init(&m->pad_types, heap_allocator());

	// TBAA
	LLVMMetadataRef root_str = LLVMMDStringInContext2(m->ctx, "Odin TBAA", 9);
	m->tbaa_root = LLVMMDNodeInContext2(m->ctx, &root_str, 1);
	m->tbaa_kind_id = LLVMGetMDKindIDInContext(m->ctx, "tbaa", 4);
	string_map_init(&m->tbaa_type_nodes);
	map_init(&m->tbaa_access_tags);

	m->const_dummy_builder = LLVMCreateBuilderInContext(m->ctx);
}

// Destroy a JIT module's resources
gb_internal void comp_destroy_jit_module(lbModule *m) {
	if (m->const_dummy_builder) {
		LLVMDisposeBuilder(m->const_dummy_builder);
	}
	if (m->target_machine) {
		LLVMDisposeTargetMachine(m->target_machine);
	}
	// Note: mod and ctx ownership is transferred to LLJIT
	// If LLJIT creation fails, caller must dispose them
}

// ---------------------------------------------------------------------------
// Collect all callees transitively from a procedure entity
// ---------------------------------------------------------------------------

gb_internal void comp_collect_callees_from_ast(Ast *node, PtrSet<Entity *> *callees);

gb_internal void comp_collect_callees_from_ast_list(Slice<Ast *> const &stmts, PtrSet<Entity *> *callees) {
	for (isize i = 0; i < stmts.count; i++) {
		if (stmts[i] != nullptr) {
			comp_collect_callees_from_ast(stmts[i], callees);
		}
	}
}

gb_internal void comp_collect_callees_from_ast(Ast *node, PtrSet<Entity *> *callees) {
	if (node == nullptr) return;

	switch (node->kind) {
	case Ast_CallExpr: {
		auto *ce = &node->CallExpr;
		Entity *callee = entity_of_node(ce->proc);
		if (callee != nullptr && callee->kind == Entity_Procedure) {
			if (!ptr_set_exists(callees, callee)) {
				ptr_set_add(callees, callee);
				// Recurse into callee's body
				DeclInfo *decl = callee->decl_info;
				if (decl != nullptr && decl->proc_lit != nullptr &&
				    decl->proc_lit->kind == Ast_ProcLit) {
					Ast *body = decl->proc_lit->ProcLit.body;
					if (body != nullptr) {
						comp_collect_callees_from_ast(body, callees);
					}
				}
			}
		}
		comp_collect_callees_from_ast(ce->proc, callees);
		comp_collect_callees_from_ast_list(ce->args, callees);
		break;
	}
	case Ast_BlockStmt:
		comp_collect_callees_from_ast_list(node->BlockStmt.stmts, callees);
		break;
	case Ast_IfStmt: {
		auto *s = &node->IfStmt;
		comp_collect_callees_from_ast(s->init, callees);
		comp_collect_callees_from_ast(s->cond, callees);
		comp_collect_callees_from_ast(s->body, callees);
		comp_collect_callees_from_ast(s->else_stmt, callees);
		break;
	}
	case Ast_ForStmt: {
		auto *s = &node->ForStmt;
		comp_collect_callees_from_ast(s->init, callees);
		comp_collect_callees_from_ast(s->cond, callees);
		comp_collect_callees_from_ast(s->post, callees);
		comp_collect_callees_from_ast(s->body, callees);
		break;
	}
	case Ast_RangeStmt: {
		auto *s = &node->RangeStmt;
		comp_collect_callees_from_ast_list(s->vals, callees);
		comp_collect_callees_from_ast(s->expr, callees);
		comp_collect_callees_from_ast(s->body, callees);
		break;
	}
	case Ast_SwitchStmt: {
		auto *s = &node->SwitchStmt;
		comp_collect_callees_from_ast(s->init, callees);
		comp_collect_callees_from_ast(s->tag,  callees);
		comp_collect_callees_from_ast(s->body, callees);
		break;
	}
	case Ast_CaseClause: {
		auto *s = &node->CaseClause;
		comp_collect_callees_from_ast_list(s->list, callees);
		comp_collect_callees_from_ast_list(s->stmts, callees);
		break;
	}
	case Ast_ReturnStmt:
		comp_collect_callees_from_ast_list(node->ReturnStmt.results, callees);
		break;
	case Ast_DeferStmt:
		comp_collect_callees_from_ast(node->DeferStmt.stmt, callees);
		break;
	case Ast_ExprStmt:
		comp_collect_callees_from_ast(node->ExprStmt.expr, callees);
		break;
	case Ast_AssignStmt: {
		auto *s = &node->AssignStmt;
		comp_collect_callees_from_ast_list(s->lhs, callees);
		comp_collect_callees_from_ast_list(s->rhs, callees);
		break;
	}
	case Ast_ValueDecl: {
		auto *vd = &node->ValueDecl;
		comp_collect_callees_from_ast_list(vd->values, callees);
		break;
	}
	case Ast_BinaryExpr: {
		auto *be = &node->BinaryExpr;
		comp_collect_callees_from_ast(be->left,  callees);
		comp_collect_callees_from_ast(be->right, callees);
		break;
	}
	case Ast_UnaryExpr:
		comp_collect_callees_from_ast(node->UnaryExpr.expr, callees);
		break;
	case Ast_ParenExpr:
		comp_collect_callees_from_ast(node->ParenExpr.expr, callees);
		break;
	case Ast_IndexExpr: {
		auto *ie = &node->IndexExpr;
		comp_collect_callees_from_ast(ie->expr,  callees);
		comp_collect_callees_from_ast(ie->index, callees);
		break;
	}
	case Ast_SliceExpr: {
		auto *se = &node->SliceExpr;
		comp_collect_callees_from_ast(se->expr, callees);
		comp_collect_callees_from_ast(se->low,  callees);
		comp_collect_callees_from_ast(se->high, callees);
		break;
	}
	case Ast_SelectorExpr:
		comp_collect_callees_from_ast(node->SelectorExpr.expr, callees);
		break;
	case Ast_CompoundLit:
		comp_collect_callees_from_ast_list(node->CompoundLit.elems, callees);
		break;
	case Ast_TypeCast: {
		auto *tc = &node->TypeCast;
		comp_collect_callees_from_ast(tc->expr, callees);
		break;
	}
	case Ast_AutoCast:
		comp_collect_callees_from_ast(node->AutoCast.expr, callees);
		break;
	case Ast_TernaryIfExpr: {
		auto *te = &node->TernaryIfExpr;
		comp_collect_callees_from_ast(te->x,    callees);
		comp_collect_callees_from_ast(te->cond, callees);
		comp_collect_callees_from_ast(te->y,    callees);
		break;
	}
	case Ast_FieldValue:
		comp_collect_callees_from_ast(node->FieldValue.value, callees);
		break;
	case Ast_WhenStmt: {
		auto *ws = &node->WhenStmt;
		comp_collect_callees_from_ast(ws->cond, callees);
		comp_collect_callees_from_ast(ws->body, callees);
		comp_collect_callees_from_ast(ws->else_stmt, callees);
		break;
	}
	case Ast_SelectorCallExpr: {
		auto *sce = &node->SelectorCallExpr;
		comp_collect_callees_from_ast(sce->expr, callees);
		comp_collect_callees_from_ast(sce->call, callees);
		break;
	}
	default:
		break;
	}
}

// ---------------------------------------------------------------------------
// JIT Symbol Resolver — maps runtime procedure names to stubs
// ---------------------------------------------------------------------------

struct CompSymbolEntry {
	char const   *name;
	void         *addr;
};

gb_global CompSymbolEntry comp_symbol_stubs[] = {
	// These names must match what the Odin codegen emits
	// We'll add a catch-all via the definition generator
	{nullptr, nullptr}, // sentinel
};

// Custom definition generator callback for LLJIT
// This resolves any unresolved symbol to the generic trap stub
static LLVMErrorRef comp_definition_generator(
	LLVMOrcDefinitionGeneratorRef GeneratorObj,
	void *Ctx,
	LLVMOrcLookupStateRef *LookupState,
	LLVMOrcLookupKind Kind,
	LLVMOrcJITDylibRef JD,
	LLVMOrcJITDylibLookupFlags JDLookupFlags,
	LLVMOrcCLookupSet Names,
	size_t NamesCount
) {
	(void)GeneratorObj; (void)Ctx; (void)LookupState;
	(void)Kind; (void)JDLookupFlags;

	// Create symbol pairs for each unresolved name, mapping to our generic trap
	auto pairs = gb_alloc_array(temporary_allocator(), LLVMOrcCSymbolMapPair, NamesCount);

	for (size_t i = 0; i < NamesCount; i++) {
		pairs[i].Name = Names[i].Name;
		pairs[i].Sym.Address = (LLVMOrcExecutorAddress)(uintptr_t)&comp_stub_generic_trap;
		pairs[i].Sym.Flags.GenericFlags = LLVMJITSymbolGenericFlagsExported;
		pairs[i].Sym.Flags.TargetFlags = 0;
	}

	LLVMOrcMaterializationUnitRef mu = LLVMOrcAbsoluteSymbols(pairs, NamesCount);
	LLVMErrorRef e = LLVMOrcJITDylibDefine(JD, mu);
	return e;
}

// ---------------------------------------------------------------------------
// Core JIT Evaluation
// ---------------------------------------------------------------------------

gb_internal CompEvalResult comp_evaluate(
	CheckerContext *ctx,
	Entity         *proc_entity,
	Type           *result_type
) {
	CompEvalResult result = {};
	result.ok = false;

	comp_ensure_llvm_initialized();

	// Create an isolated JIT generator.
	// The module lives as gen.default_module so that code generation lookups
	// (lb_find_value, lb_find_procedure_value_from_entity, etc.) that
	// fall back to gen->default_module will find our module's LLVM module.
	lbGenerator comp_gen = {};
	comp_gen.info = &ctx->checker->info;
	map_init(&comp_gen.modules);
	map_init(&comp_gen.modules_through_ctx);
	lbModule &comp_module = comp_gen.default_module;
	comp_init_jit_module(&comp_module, ctx->checker);
	comp_module.gen = &comp_gen;

	// Collect all procedures in the call graph
	auto callees = PtrSet<Entity *>{};
	ptr_set_init(&callees, 64);
	defer (ptr_set_destroy(&callees));

	ptr_set_add(&callees, proc_entity);

	DeclInfo *decl = proc_entity->decl_info;
	if (decl != nullptr && decl->proc_lit != nullptr &&
	    decl->proc_lit->kind == Ast_ProcLit) {
		Ast *body = decl->proc_lit->ProcLit.body;
		if (body != nullptr) {
			comp_collect_callees_from_ast(body, &callees);
		}
	}

	// Create procedures in the JIT module
	lbProcedure *entry_proc = nullptr;
	FOR_PTR_SET(e, callees) {
		if (e->kind != Entity_Procedure) continue;
		lbProcedure *p = lb_create_procedure(&comp_module, e);
		if (p != nullptr && e == proc_entity) {
			entry_proc = p;
		}
	}

	if (entry_proc == nullptr) {
		result.panic_msg = str_lit("failed to create procedure for #comp evaluation");
		comp_destroy_jit_module(&comp_module);
		LLVMContextDispose(comp_module.ctx);
		return result;
	}

	// Generate procedure bodies.
	// Disable bounds checking since runtime error procedures aren't available
	// in the JIT module. Our longjmp trap stubs catch actual errors at execution.
	bool saved_no_bounds_check = build_context.no_bounds_check;
	build_context.no_bounds_check = true;

	FOR_PTR_SET(e, callees) {
		if (e->kind != Entity_Procedure) continue;
		if (e->Procedure.is_foreign) continue; // Skip foreign procs — will be resolved by stubs

		lbProcedure *p = nullptr;
		String name = lb_get_entity_name(&comp_module, e);
		lbProcedure **found = string_map_get(&comp_module.procedures, name);
		if (found != nullptr) {
			p = *found;
		}
		if (p != nullptr) {
			lb_generate_procedure(&comp_module, p);
		}
	}

	build_context.no_bounds_check = saved_no_bounds_check;
	// Create a wrapper function that calls the target and stores the result
	// to a buffer, avoiding ABI issues with struct/float returns.
	// Wrapper signature: void __comp_wrapper(i8* result_buf)
	char const *wrapper_name = "__comp_eval_wrapper";
	{
		LLVMTypeRef target_fn_type = LLVMGlobalGetValueType(entry_proc->value);
		LLVMTypeRef target_ret_type = LLVMGetReturnType(target_fn_type);
		unsigned target_param_count = LLVMCountParamTypes(target_fn_type);
		bool uses_sret = (LLVMGetTypeKind(target_ret_type) == LLVMVoidTypeKind && target_param_count > 0);

		LLVMTypeRef ptr_type = LLVMPointerTypeInContext(comp_module.ctx, 0);
		LLVMTypeRef void_type = LLVMVoidTypeInContext(comp_module.ctx);
		LLVMTypeRef wrapper_param_types[] = { ptr_type };
		LLVMTypeRef wrapper_type = LLVMFunctionType(void_type, wrapper_param_types, 1, false);
		LLVMValueRef wrapper_fn = LLVMAddFunction(comp_module.mod, wrapper_name, wrapper_type);
		LLVMSetLinkage(wrapper_fn, LLVMExternalLinkage);

		LLVMBasicBlockRef bb = LLVMAppendBasicBlockInContext(comp_module.ctx, wrapper_fn, "entry");
		LLVMBuilderRef builder = LLVMCreateBuilderInContext(comp_module.ctx);
		LLVMPositionBuilderAtEnd(builder, bb);

		LLVMValueRef buf_ptr = LLVMGetParam(wrapper_fn, 0);

		if (uses_sret) {
			// The target function takes an sret pointer as first arg and returns void.
			// Pass our buffer pointer as the sret argument.
			LLVMValueRef args[] = { buf_ptr };
			LLVMBuildCall2(builder, target_fn_type, entry_proc->value, args, 1, "");
		} else {
			// Direct return — call and store the result.
			LLVMValueRef call_result = LLVMBuildCall2(builder, target_fn_type, entry_proc->value, nullptr, 0, "");
			LLVMBuildStore(builder, call_result, buf_ptr);
		}

		LLVMBuildRetVoid(builder);
		LLVMDisposeBuilder(builder);
	}

	// Run minimal optimization passes
	{
		LLVMPassBuilderOptionsRef pb_opts = LLVMCreatePassBuilderOptions();
		LLVMRunPasses(comp_module.mod,
			"function(sroa,early-cse,simplifycfg,instcombine,simplifycfg)",
			comp_module.target_machine, pb_opts);
		LLVMDisposePassBuilderOptions(pb_opts);
	}

	// Create LLJIT
	LLVMOrcLLJITRef jit = nullptr;
	{
		LLVMOrcLLJITBuilderRef builder = LLVMOrcCreateLLJITBuilder();
		LLVMErrorRef err = LLVMOrcCreateLLJIT(&jit, builder);
		if (err) {
			char *msg = LLVMGetErrorMessage(err);
			result.panic_msg = copy_string(permanent_allocator(), make_string_c(msg));
			LLVMDisposeErrorMessage(msg);
			LLVMDisposeModule(comp_module.mod);
			LLVMContextDispose(comp_module.ctx);
			comp_destroy_jit_module(&comp_module);
			return result;
		}
	}

	// Register symbol resolver for runtime stubs
	{
		LLVMOrcJITDylibRef dylib = LLVMOrcLLJITGetMainJITDylib(jit);
		LLVMOrcDefinitionGeneratorRef gen = nullptr;
		gen = LLVMOrcCreateCustomCAPIDefinitionGenerator(comp_definition_generator, nullptr, nullptr);
		LLVMOrcJITDylibAddGenerator(dylib, gen);
	}

	// Wrap module in ThreadSafeModule and add to JIT.
	{
		LLVMOrcThreadSafeContextRef ts_ctx =
			LLVMOrcCreateNewThreadSafeContextFromLLVMContext(comp_module.ctx);
		comp_module.ctx = nullptr; // ownership transferred

		LLVMOrcThreadSafeModuleRef ts_mod =
			LLVMOrcCreateNewThreadSafeModule(comp_module.mod, ts_ctx);
		comp_module.mod = nullptr; // ownership transferred

		LLVMOrcDisposeThreadSafeContext(ts_ctx);

		LLVMOrcJITDylibRef dylib = LLVMOrcLLJITGetMainJITDylib(jit);
		LLVMErrorRef err = LLVMOrcLLJITAddLLVMIRModule(jit, dylib, ts_mod);
		if (err) {
			char *msg = LLVMGetErrorMessage(err);
			result.panic_msg = copy_string(permanent_allocator(), make_string_c(msg));
			LLVMDisposeErrorMessage(msg);
			LLVMOrcDisposeLLJIT(jit);
			comp_destroy_jit_module(&comp_module);
			return result;
		}
	}

	// Look up the wrapper function
	LLVMOrcExecutorAddress fn_addr = 0;
	{
		LLVMErrorRef err = LLVMOrcLLJITLookup(jit, &fn_addr, wrapper_name);
		if (err) {
			char *msg = LLVMGetErrorMessage(err);
			result.panic_msg = copy_string(permanent_allocator(), make_string_c(msg));
			LLVMDisposeErrorMessage(msg);
			LLVMOrcDisposeLLJIT(jit);
			comp_destroy_jit_module(&comp_module);
			return result;
		}
	}

	if (fn_addr == 0) {
		result.panic_msg = str_lit("failed to look up #comp wrapper in JIT");
		LLVMOrcDisposeLLJIT(jit);
		comp_destroy_jit_module(&comp_module);
		return result;
	}

	// Execute the wrapper function
	i64 result_size = type_size_of(result_type);
	u8 *result_buf = gb_alloc_array(permanent_allocator(), u8, result_size);
	gb_memset(result_buf, 0, cast(isize)result_size);

	if (setjmp(comp_trap_state.recovery) == 0) {
		comp_trap_state.panicked = false;
		comp_trap_state.panic_msg[0] = 0;

		typedef void (*CompWrapperFn)(void *);
		auto fn = (CompWrapperFn)(uintptr_t)fn_addr;
		fn(result_buf);

		// Convert results to ExactValue
		Type *bt = base_type(result_type);
		if (is_type_integer(bt) || is_type_enum(bt)) {
			Type *inner = bt;
			if (is_type_enum(bt)) inner = base_type(bt->Enum.base_type);
			if (result_size > 8) {
				// 128-bit integers — use raw bytes
				result.value = exact_value_raw_bytes(result_buf, result_size);
			} else {
				u64 val = 0;
				gb_memmove(&val, result_buf, cast(isize)result_size);
				if (is_type_unsigned(inner)) {
					result.value = exact_value_u64(val);
				} else {
					i64 sval = 0;
					gb_memmove(&sval, result_buf, cast(isize)result_size);
					if (result_size < 8) {
						i64 shift = (8 - result_size) * 8;
						sval = (sval << shift) >> shift;
					}
					result.value = exact_value_i64(sval);
				}
			}
		} else if (is_type_float(bt)) {
			if (result_size == 2) {
				result.value = exact_value_raw_bytes(result_buf, result_size);
			} else if (result_size == 4) {
				f32 val;
				gb_memmove(&val, result_buf, 4);
				result.value = exact_value_float((f64)val);
			} else if (result_size == 8) {
				f64 val;
				gb_memmove(&val, result_buf, 8);
				result.value = exact_value_float(val);
			} else {
				result.value = exact_value_raw_bytes(result_buf, result_size);
			}
		} else if (is_type_boolean(bt)) {
			result.value = exact_value_bool(result_buf[0] != 0);
		} else {
			// Struct, array, etc. — use raw bytes
			result.value = exact_value_raw_bytes(result_buf, result_size);
		}
		result.ok = true;
	} else {
		// longjmp landed here — function panicked
		result.ok = false;
		result.panic_msg = copy_string(permanent_allocator(),
			make_string_c(comp_trap_state.panic_msg));
	}

	// Clean up
	LLVMOrcDisposeLLJIT(jit);
	comp_destroy_jit_module(&comp_module);

	return result;
}

// ---------------------------------------------------------------------------
// Timeout Wrapper
// ---------------------------------------------------------------------------

gb_internal CompEvalResult comp_evaluate_with_timeout(
	CheckerContext *ctx,
	Entity         *proc_entity,
	Type           *result_type,
	f64             timeout_seconds
) {
	CompEvalResult result = {};
	result.ok = false;

	bool finished = false;
	std::mutex mtx;
	std::condition_variable cv;

	std::thread worker([&]() {
		result = comp_evaluate(ctx, proc_entity, result_type);
		{
			std::lock_guard<std::mutex> lock(mtx);
			finished = true;
		}
		cv.notify_one();
	});

	{
		std::unique_lock<std::mutex> lock(mtx);
		if (!cv.wait_for(lock, std::chrono::duration<f64>(timeout_seconds), [&]{ return finished; })) {
			// Timeout
			result.ok = false;
			result.panic_msg = str_lit("timed out");
			// Detach the worker thread — it will be cleaned up at process exit
			worker.detach();
			return result;
		}
	}

	if (worker.joinable()) {
		worker.join();
	}

	return result;
}
