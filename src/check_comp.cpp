// check_comp.cpp — Purity analysis and return type validation for #comp

// Forward declaration — defined later in checker.cpp
gb_internal bool check_proc_info(Checker *c, ProcInfo *pi, UntypedExprInfoMap *untyped);

enum CompImpurityKind {
	CompImpure_None,
	CompImpure_ContextAccess,
	CompImpure_ForeignCall,
	CompImpure_PointerType,
	CompImpure_SliceType,
	CompImpure_DynamicArrayType,
	CompImpure_MapType,
	CompImpure_Allocation,
	CompImpure_Transmute,
	CompImpure_ProcParameter,
	CompImpure_GlobalMutable,
	CompImpure_TargetDependent,
};

struct CompImpurityTrace {
	Entity *        proc;
	Token           call_site;
	CompImpurityKind kind;
	Token           violation_site;
	String          detail;
};

gb_internal char const *comp_impurity_message(CompImpurityTrace const &t) {
	switch (t.kind) {
	case CompImpure_None:            return "no violation";
	case CompImpure_ContextAccess:   return "uses 'context' (implicit parameter)";
	case CompImpure_ForeignCall:     return "is a foreign procedure and cannot be evaluated at compile time";
	case CompImpure_PointerType:     return "pointer type is not allowed in #comp procedures";
	case CompImpure_SliceType:       return "slice type is not allowed in #comp procedures (use a fixed-size array)";
	case CompImpure_DynamicArrayType:return "dynamic array type is not allowed in #comp procedures";
	case CompImpure_MapType:         return "map type is not allowed in #comp procedures";
	case CompImpure_Allocation:      return "requires an allocator from 'context'";
	case CompImpure_Transmute:       return "'transmute' is target-dependent and not allowed in #comp procedures";
	case CompImpure_ProcParameter:   return "procedure parameter cannot be checked for purity";
	case CompImpure_GlobalMutable:   return "mutable global variable access is not allowed in #comp procedures";
	case CompImpure_TargetDependent: return "target-dependent type is not allowed in #comp procedures (use fixed-width types)";
	}
	return "unknown violation";
}

// Forward declarations
gb_internal bool check_comp_purity_proc(Entity *proc_entity, PtrSet<Entity *> *visited, Array<CompImpurityTrace> *trace);
gb_internal bool check_comp_type_pure(Type *t, Token site, Entity *proc_entity, Array<CompImpurityTrace> *trace);
gb_internal bool comp_record_impurity(Array<CompImpurityTrace> *trace, Entity *proc, CompImpurityKind kind, Token site);

// Check whether a type is valid for #comp return values (can be a compile-time constant).
gb_internal bool is_comp_constant_type(Type *t) {
	t = base_type(t);
	if (t == nullptr) return false;

	switch (t->kind) {
	case Type_Basic:
		if (t->Basic.flags & BasicFlag_Untyped) return false;
		if (t == t_int || t == t_uint || t == t_uintptr) return false;
		if (t->Basic.flags & BasicFlag_Pointer) return false; // rawptr
		if (t->Basic.flags & BasicFlag_String) return false;  // string contains pointer
		if (is_type_integer(t))  return true;
		if (is_type_float(t))    return true;
		if (is_type_boolean(t))  return true;
		return false;
	case Type_Enum:
		return is_comp_constant_type(t->Enum.base_type);
	case Type_Array:
		return is_comp_constant_type(t->Array.elem);
	case Type_Struct:
		if (t->Struct.is_raw_union) return false;
		for (isize i = 0; i < t->Struct.fields.count; i++) {
			if (!is_comp_constant_type(t->Struct.fields[i]->type)) return false;
		}
		return true;
	default:
		return false; // Pointer, Slice, DynamicArray, Map, Proc, etc.
	}
}

// Check whether a type is target-dependent (int, uint, uintptr).
gb_internal bool is_comp_target_dependent_type(Type *t) {
	t = base_type(t);
	if (t == nullptr) return false;
	return t == t_int || t == t_uint || t == t_uintptr;
}

// Check whether a type contains any impure constructs (pointers, slices, etc.)
// Returns true if the type is pure, false if impure (with trace populated).
gb_internal bool check_comp_type_pure(Type *t, Token site, Entity *proc_entity, Array<CompImpurityTrace> *trace) {
	if (t == nullptr) return true;
	t = base_type(t);

	if (is_type_pointer(t) || (t->kind == Type_Basic && (t->Basic.flags & BasicFlag_Pointer))) {
		return comp_record_impurity(trace, proc_entity, CompImpure_PointerType, site);
	}
	if (is_type_slice(t)) {
		return comp_record_impurity(trace, proc_entity, CompImpure_SliceType, site);
	}
	if (is_type_dynamic_array(t)) {
		return comp_record_impurity(trace, proc_entity, CompImpure_DynamicArrayType, site);
	}
	if (is_type_map(t)) {
		return comp_record_impurity(trace, proc_entity, CompImpure_MapType, site);
	}
	if (is_comp_target_dependent_type(t)) {
		return comp_record_impurity(trace, proc_entity, CompImpure_TargetDependent, site);
	}

	// Recurse into composite types
	if (t->kind == Type_Array) {
		return check_comp_type_pure(t->Array.elem, site, proc_entity, trace);
	}
	if (t->kind == Type_Struct) {
		for (isize i = 0; i < t->Struct.fields.count; i++) {
			if (!check_comp_type_pure(t->Struct.fields[i]->type, site, proc_entity, trace)) {
				return false;
			}
		}
	}
	if (t->kind == Type_Enum) {
		return check_comp_type_pure(t->Enum.base_type, site, proc_entity, trace);
	}

	return true;
}

// Record an impurity and return false.
gb_internal bool comp_record_impurity(Array<CompImpurityTrace> *trace, Entity *proc, CompImpurityKind kind, Token site) {
	CompImpurityTrace entry = {};
	entry.proc = proc;
	entry.kind = kind;
	entry.violation_site = site;
	array_add(trace, entry);
	return false;
}

// Walk a single AST node for purity violations.
// Returns true if pure, false if impure.
gb_internal bool check_comp_purity_ast(Ast *node, Entity *proc_entity, PtrSet<Entity *> *visited, Array<CompImpurityTrace> *trace);

gb_internal bool check_comp_purity_ast_list(Slice<Ast *> const &stmts, Entity *proc_entity, PtrSet<Entity *> *visited, Array<CompImpurityTrace> *trace) {
	for (isize i = 0; i < stmts.count; i++) {
		if (stmts[i] == nullptr) continue;
		if (!check_comp_purity_ast(stmts[i], proc_entity, visited, trace)) {
			return false;
		}
	}
	return true;
}

gb_internal bool check_comp_purity_ast(Ast *node, Entity *proc_entity, PtrSet<Entity *> *visited, Array<CompImpurityTrace> *trace) {
	if (node == nullptr) return true;

	switch (node->kind) {
	case Ast_Invalid:
	case Ast_Ident: {
		Entity *e = entity_of_node(node);
		if (e == nullptr) break;
		// Check for global mutable variable access
		if (e->kind == Entity_Variable && e->Variable.is_global) {
			return comp_record_impurity(trace, proc_entity, CompImpure_GlobalMutable, node->Ident.token);
		}
		// Check type of referenced entity
		if (e->type != nullptr) {
			if (!check_comp_type_pure(e->type, node->Ident.token, proc_entity, trace)) {
				return false;
			}
		}
		break;
	}
	case Ast_Implicit: {
		if (node->Implicit.kind == Token_context) {
			return comp_record_impurity(trace, proc_entity, CompImpure_ContextAccess, node->Implicit);
		}
		break;
	}
	case Ast_BasicLit:
	case Ast_BasicDirective:
		break;

	case Ast_CompoundLit: {
		auto *cl = &node->CompoundLit;
		if (cl->type != nullptr) {
			if (!check_comp_purity_ast(cl->type, proc_entity, visited, trace)) return false;
		}
		if (!check_comp_purity_ast_list(cl->elems, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_ProcLit: {
		// Procedure literals within a #comp function would capture closures — not pure.
		// But actually, nested proc lits that don't capture anything should be fine IF they're pure.
		// For safety, reject proc literals in #comp for now (they're never needed for table generation).
		return comp_record_impurity(trace, proc_entity, CompImpure_ProcParameter, ast_token(node));
	}

	case Ast_UnaryExpr: {
		auto *ue = &node->UnaryExpr;
		if (ue->op.kind == Token_And) { // address-of
			return comp_record_impurity(trace, proc_entity, CompImpure_PointerType, ue->op);
		}
		if (!check_comp_purity_ast(ue->expr, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_BinaryExpr: {
		auto *be = &node->BinaryExpr;
		if (!check_comp_purity_ast(be->left,  proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(be->right, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_ParenExpr: {
		if (!check_comp_purity_ast(node->ParenExpr.expr, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_SelectorExpr: {
		if (!check_comp_purity_ast(node->SelectorExpr.expr, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_SelectorCallExpr: {
		auto *sce = &node->SelectorCallExpr;
		if (!check_comp_purity_ast(sce->expr, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(sce->call, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_IndexExpr: {
		auto *ie = &node->IndexExpr;
		if (!check_comp_purity_ast(ie->expr,  proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(ie->index, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_SliceExpr: {
		auto *se = &node->SliceExpr;
		if (!check_comp_purity_ast(se->expr, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(se->low,  proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(se->high, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_DerefExpr: {
		// Dereferencing a pointer — pointers are not allowed
		return comp_record_impurity(trace, proc_entity, CompImpure_PointerType, node->DerefExpr.op);
	}
	case Ast_CallExpr: {
		auto *ce = &node->CallExpr;
		// Check arguments first
		if (!check_comp_purity_ast_list(ce->args, proc_entity, visited, trace)) return false;

		// Resolve callee
		Ast *proc_node = ce->proc;
		Entity *callee = entity_of_node(proc_node);
		if (callee != nullptr) {
			if (callee->kind == Entity_Builtin) {
				// Check for allocation builtins
				i32 id = callee->Builtin.id;
				// size_of, align_of are fine — but check for target-dependent arguments
				// make, new, append, delete, free are NOT in the builtin enum
				// They're regular procedures in the runtime, so they'll be caught by the call graph walk
				break;
			}
			if (callee->kind == Entity_Procedure) {
				// Recursively check callee purity
				if (!check_comp_purity_proc(callee, visited, trace)) {
					// Add our position to the chain
					CompImpurityTrace entry = {};
					entry.proc = proc_entity;
					entry.call_site = ce->open;
					entry.kind = CompImpure_None; // chain link, not the violation itself
					array_add(trace, entry);
					return false;
				}
				break;
			}
			if (callee->kind == Entity_ProcGroup) {
				// Proc groups — the actual callee is resolved during checking.
				// We can't statically verify purity for proc groups here because the
				// specific overload isn't known from the AST alone.
				// During checker integration, the resolved entity will be checked instead.
				break;
			}
		}
		// If callee can't be resolved, check the proc expression
		if (!check_comp_purity_ast(proc_node, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_TypeCast: {
		auto *tc = &node->TypeCast;
		if (tc->token.kind == Token_transmute) {
			return comp_record_impurity(trace, proc_entity, CompImpure_Transmute, tc->token);
		}
		if (!check_comp_purity_ast(tc->type, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(tc->expr, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_AutoCast: {
		if (!check_comp_purity_ast(node->AutoCast.expr, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_TernaryIfExpr: {
		auto *te = &node->TernaryIfExpr;
		if (!check_comp_purity_ast(te->x,    proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(te->cond, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(te->y,    proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_TernaryWhenExpr: {
		auto *te = &node->TernaryWhenExpr;
		if (!check_comp_purity_ast(te->x,    proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(te->cond, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(te->y,    proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_OrElseExpr: {
		if (!check_comp_purity_ast(node->OrElseExpr.x, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(node->OrElseExpr.y, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_OrReturnExpr: {
		if (!check_comp_purity_ast(node->OrReturnExpr.expr, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_FieldValue: {
		if (!check_comp_purity_ast(node->FieldValue.field, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(node->FieldValue.value, proc_entity, visited, trace)) return false;
		break;
	}

	// Statements
	case Ast_EmptyStmt:
		break;
	case Ast_ExprStmt: {
		if (!check_comp_purity_ast(node->ExprStmt.expr, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_AssignStmt: {
		auto *as = &node->AssignStmt;
		if (!check_comp_purity_ast_list(as->lhs, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast_list(as->rhs, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_BlockStmt: {
		if (!check_comp_purity_ast_list(node->BlockStmt.stmts, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_IfStmt: {
		auto *is_ = &node->IfStmt;
		if (!check_comp_purity_ast(is_->init, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(is_->cond, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(is_->body, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(is_->else_stmt, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_WhenStmt: {
		auto *ws = &node->WhenStmt;
		// Only check the condition — the taken branch is determined at compile time
		if (!check_comp_purity_ast(ws->cond, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(ws->body, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(ws->else_stmt, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_ReturnStmt: {
		if (!check_comp_purity_ast_list(node->ReturnStmt.results, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_ForStmt: {
		auto *fs = &node->ForStmt;
		if (!check_comp_purity_ast(fs->init, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(fs->cond, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(fs->post, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(fs->body, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_RangeStmt: {
		auto *rs = &node->RangeStmt;
		if (!check_comp_purity_ast_list(rs->vals, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(rs->expr, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(rs->body, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_SwitchStmt: {
		auto *ss = &node->SwitchStmt;
		if (!check_comp_purity_ast(ss->init, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(ss->tag,  proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(ss->body, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_CaseClause: {
		auto *cc = &node->CaseClause;
		if (!check_comp_purity_ast_list(cc->list, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast_list(cc->stmts, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_DeferStmt: {
		if (!check_comp_purity_ast(node->DeferStmt.stmt, proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_BranchStmt:
		break;
	case Ast_ValueDecl: {
		auto *vd = &node->ValueDecl;
		if (vd->type != nullptr) {
			if (!check_comp_purity_ast(vd->type, proc_entity, visited, trace)) return false;
		}
		if (!check_comp_purity_ast_list(vd->values, proc_entity, visited, trace)) return false;
		break;
	}

	// Types — check for impure types in type expressions
	case Ast_PointerType:
		return comp_record_impurity(trace, proc_entity, CompImpure_PointerType, node->PointerType.token);
	case Ast_MultiPointerType:
		return comp_record_impurity(trace, proc_entity, CompImpure_PointerType, node->MultiPointerType.token);
	case Ast_ArrayType: {
		if (!check_comp_purity_ast(node->ArrayType.count, proc_entity, visited, trace)) return false;
		if (!check_comp_purity_ast(node->ArrayType.elem,  proc_entity, visited, trace)) return false;
		break;
	}
	case Ast_DynamicArrayType:
		return comp_record_impurity(trace, proc_entity, CompImpure_DynamicArrayType, node->DynamicArrayType.token);
	case Ast_MapType:
		return comp_record_impurity(trace, proc_entity, CompImpure_MapType, node->MapType.token);

	case Ast_InlineAsmExpr:
		return comp_record_impurity(trace, proc_entity, CompImpure_ForeignCall, ast_token(node));

	default:
		// For any unhandled node kinds, assume pure.
		// The type checker and the purity of called procedures
		// will catch actual violations.
		break;
	}
	return true;
}

// Check purity of a single procedure entity.
// Returns true if pure, false if impure (with trace populated).
gb_internal bool check_comp_purity_proc(Entity *proc_entity, PtrSet<Entity *> *visited, Array<CompImpurityTrace> *trace) {
	if (proc_entity == nullptr) return true;
	if (proc_entity->kind != Entity_Procedure) return true;

	// Already visited — pure (no cycles in pure call graphs)
	if (ptr_set_exists(visited, proc_entity)) return true;
	ptr_set_add(visited, proc_entity);

	// Foreign procedure — impure
	if (proc_entity->Procedure.is_foreign) {
		return comp_record_impurity(trace, proc_entity, CompImpure_ForeignCall, proc_entity->token);
	}

	// Check parameter types for procedure-type parameters
	Type *sig = proc_entity->type;
	if (sig != nullptr && sig->kind == Type_Proc) {
		if (sig->Proc.params != nullptr) {
			TypeTuple *params = &sig->Proc.params->Tuple;
			for (isize i = 0; i < params->variables.count; i++) {
				Entity *param = params->variables[i];
				if (param->type != nullptr && param->type->kind == Type_Proc) {
					return comp_record_impurity(trace, proc_entity, CompImpure_ProcParameter, param->token);
				}
				// Check param type for pointers, slices, etc.
				if (!check_comp_type_pure(param->type, param->token, proc_entity, trace)) {
					return false;
				}
			}
		}

		// Check return type
		if (sig->Proc.results != nullptr) {
			TypeTuple *results = &sig->Proc.results->Tuple;
			for (isize i = 0; i < results->variables.count; i++) {
				Entity *result = results->variables[i];
				if (!check_comp_type_pure(result->type, result->token, proc_entity, trace)) {
					return false;
				}
			}
		}

		// Note: context access is caught by the AST walk (Ast_Implicit with Token_context).
		// We don't reject non-contextless procedures at the signature level because
		// many pure functions are declared without "contextless" but don't actually use context.
	}

	// Get the procedure body
	DeclInfo *decl = proc_entity->decl_info;
	if (decl == nullptr) return true;

	Ast *proc_lit = decl->proc_lit;
	if (proc_lit == nullptr) return true;
	if (proc_lit->kind != Ast_ProcLit) return true;

	Ast *body = proc_lit->ProcLit.body;
	if (body == nullptr) return true; // No body — likely a foreign proc, caught above

	// Walk the body
	return check_comp_purity_ast(body, proc_entity, visited, trace);
}

// Entry point: Check purity of a procedure for #comp.
gb_internal bool check_comp_purity(CheckerContext *ctx, Entity *proc_entity, Ast *comp_call_site, Array<CompImpurityTrace> *trace) {
	auto visited = PtrSet<Entity *>{};
	ptr_set_init(&visited, 64);
	defer (ptr_set_destroy(&visited));

	return check_comp_purity_proc(proc_entity, &visited, trace);
}

// Report purity errors with the full call chain.
gb_internal void report_comp_purity_error(CheckerContext *ctx, Ast *comp_call_site, Array<CompImpurityTrace> const &trace) {
	ERROR_BLOCK();

	if (trace.count == 0) return;

	// The first entry in the trace is the deepest violation
	CompImpurityTrace const &violation = trace[0];

	error(violation.violation_site,
		"procedure '%.*s' is not pure: %s",
		LIT(violation.proc->token.string),
		comp_impurity_message(violation));

	// Print call chain from violation back to #comp site
	// trace[0] = violation, trace[1..n] = chain links (callers)
	for (isize i = 1; i < trace.count; i++) {
		CompImpurityTrace const &link = trace[i];
		CompImpurityTrace const &callee = trace[i-1];
		error_line("\tnote: '%.*s' calls '%.*s' at %s\n",
			LIT(link.proc->token.string),
			LIT(callee.proc->token.string),
			token_pos_to_string(link.call_site.pos));
	}

	error_line("\tnote: required by '#comp' at %s\n",
		token_pos_to_string(ast_token(comp_call_site).pos));
}

// Force a single procedure's body to be type-checked.
gb_internal void comp_force_check_one(Checker *checker, Entity *proc_entity) {
	if (proc_entity == nullptr || proc_entity->kind != Entity_Procedure) return;
	if (proc_entity->Procedure.is_foreign) return;
	if ((proc_entity->flags & EntityFlag_ProcBodyChecked) != 0) return;

	DeclInfo *decl = proc_entity->decl_info;
	if (decl == nullptr) return;

	Ast *proc_lit = decl->proc_lit;
	if (proc_lit == nullptr || proc_lit->kind != Ast_ProcLit) return;

	ProcInfo pi = {};
	pi.file  = proc_entity->file;
	pi.token = proc_entity->token;
	pi.decl  = decl;
	pi.type  = proc_entity->type;
	pi.body  = proc_lit->ProcLit.body;
	pi.tags  = proc_lit->ProcLit.tags;

	if (pi.body == nullptr) return;

	UntypedExprInfoMap untyped = {};
	check_proc_info(checker, &pi, &untyped);
	map_destroy(&untyped);
}

// Collect callee entities from an AST and force-check their bodies.
gb_internal void comp_ensure_callees_checked(Checker *checker, Ast *node, PtrSet<Entity *> *visited);

gb_internal void comp_ensure_callees_checked_list(Checker *checker, Slice<Ast *> const &stmts, PtrSet<Entity *> *visited) {
	for (isize i = 0; i < stmts.count; i++) {
		if (stmts[i] != nullptr) {
			comp_ensure_callees_checked(checker, stmts[i], visited);
		}
	}
}

gb_internal void comp_ensure_callees_checked(Checker *checker, Ast *node, PtrSet<Entity *> *visited) {
	if (node == nullptr) return;

	switch (node->kind) {
	case Ast_CallExpr: {
		auto *ce = &node->CallExpr;
		Entity *callee = entity_of_node(ce->proc);
		if (callee != nullptr && callee->kind == Entity_Procedure) {
			if (!ptr_set_exists(visited, callee)) {
				ptr_set_add(visited, callee);
				comp_force_check_one(checker, callee);
				// Recurse into callee's body
				DeclInfo *decl = callee->decl_info;
				if (decl != nullptr && decl->proc_lit != nullptr &&
				    decl->proc_lit->kind == Ast_ProcLit) {
					Ast *body = decl->proc_lit->ProcLit.body;
					if (body != nullptr) {
						comp_ensure_callees_checked(checker, body, visited);
					}
				}
			}
		}
		comp_ensure_callees_checked(checker, ce->proc, visited);
		comp_ensure_callees_checked_list(checker, ce->args, visited);
		break;
	}
	case Ast_BlockStmt:
		comp_ensure_callees_checked_list(checker, node->BlockStmt.stmts, visited);
		break;
	case Ast_IfStmt: {
		auto *s = &node->IfStmt;
		comp_ensure_callees_checked(checker, s->init, visited);
		comp_ensure_callees_checked(checker, s->cond, visited);
		comp_ensure_callees_checked(checker, s->body, visited);
		comp_ensure_callees_checked(checker, s->else_stmt, visited);
		break;
	}
	case Ast_ForStmt: {
		auto *s = &node->ForStmt;
		comp_ensure_callees_checked(checker, s->init, visited);
		comp_ensure_callees_checked(checker, s->cond, visited);
		comp_ensure_callees_checked(checker, s->post, visited);
		comp_ensure_callees_checked(checker, s->body, visited);
		break;
	}
	case Ast_RangeStmt: {
		auto *s = &node->RangeStmt;
		comp_ensure_callees_checked_list(checker, s->vals, visited);
		comp_ensure_callees_checked(checker, s->expr, visited);
		comp_ensure_callees_checked(checker, s->body, visited);
		break;
	}
	case Ast_SwitchStmt: {
		auto *s = &node->SwitchStmt;
		comp_ensure_callees_checked(checker, s->init, visited);
		comp_ensure_callees_checked(checker, s->tag,  visited);
		comp_ensure_callees_checked(checker, s->body, visited);
		break;
	}
	case Ast_CaseClause: {
		auto *s = &node->CaseClause;
		comp_ensure_callees_checked_list(checker, s->list, visited);
		comp_ensure_callees_checked_list(checker, s->stmts, visited);
		break;
	}
	case Ast_ReturnStmt:
		comp_ensure_callees_checked_list(checker, node->ReturnStmt.results, visited);
		break;
	case Ast_DeferStmt:
		comp_ensure_callees_checked(checker, node->DeferStmt.stmt, visited);
		break;
	case Ast_ExprStmt:
		comp_ensure_callees_checked(checker, node->ExprStmt.expr, visited);
		break;
	case Ast_AssignStmt: {
		auto *s = &node->AssignStmt;
		comp_ensure_callees_checked_list(checker, s->lhs, visited);
		comp_ensure_callees_checked_list(checker, s->rhs, visited);
		break;
	}
	case Ast_ValueDecl:
		comp_ensure_callees_checked_list(checker, node->ValueDecl.values, visited);
		break;
	case Ast_BinaryExpr:
		comp_ensure_callees_checked(checker, node->BinaryExpr.left,  visited);
		comp_ensure_callees_checked(checker, node->BinaryExpr.right, visited);
		break;
	case Ast_UnaryExpr:
		comp_ensure_callees_checked(checker, node->UnaryExpr.expr, visited);
		break;
	case Ast_ParenExpr:
		comp_ensure_callees_checked(checker, node->ParenExpr.expr, visited);
		break;
	case Ast_IndexExpr:
		comp_ensure_callees_checked(checker, node->IndexExpr.expr,  visited);
		comp_ensure_callees_checked(checker, node->IndexExpr.index, visited);
		break;
	case Ast_SliceExpr: {
		auto *se = &node->SliceExpr;
		comp_ensure_callees_checked(checker, se->expr, visited);
		comp_ensure_callees_checked(checker, se->low,  visited);
		comp_ensure_callees_checked(checker, se->high, visited);
		break;
	}
	case Ast_SelectorExpr:
		comp_ensure_callees_checked(checker, node->SelectorExpr.expr, visited);
		break;
	case Ast_SelectorCallExpr: {
		auto *sce = &node->SelectorCallExpr;
		comp_ensure_callees_checked(checker, sce->expr, visited);
		comp_ensure_callees_checked(checker, sce->call, visited);
		break;
	}
	case Ast_CompoundLit:
		comp_ensure_callees_checked_list(checker, node->CompoundLit.elems, visited);
		break;
	case Ast_TypeCast:
		comp_ensure_callees_checked(checker, node->TypeCast.expr, visited);
		break;
	case Ast_AutoCast:
		comp_ensure_callees_checked(checker, node->AutoCast.expr, visited);
		break;
	case Ast_TernaryIfExpr:
		comp_ensure_callees_checked(checker, node->TernaryIfExpr.x,    visited);
		comp_ensure_callees_checked(checker, node->TernaryIfExpr.cond, visited);
		comp_ensure_callees_checked(checker, node->TernaryIfExpr.y,    visited);
		break;
	case Ast_FieldValue:
		comp_ensure_callees_checked(checker, node->FieldValue.value, visited);
		break;
	case Ast_WhenStmt: {
		auto *ws = &node->WhenStmt;
		comp_ensure_callees_checked(checker, ws->cond, visited);
		comp_ensure_callees_checked(checker, ws->body, visited);
		comp_ensure_callees_checked(checker, ws->else_stmt, visited);
		break;
	}
	default:
		break;
	}
}

// Force a procedure's body and all transitive callees to be type-checked.
// This is necessary because #comp evaluation may run during entity checking,
// before the callee's body has been checked in the normal checker order.
gb_internal void comp_ensure_body_checked(CheckerContext *ctx, Entity *proc_entity) {
	if (proc_entity == nullptr || proc_entity->kind != Entity_Procedure) return;
	if (proc_entity->Procedure.is_foreign) return;

	auto visited = PtrSet<Entity *>{};
	ptr_set_init(&visited, 64);
	defer (ptr_set_destroy(&visited));

	ptr_set_add(&visited, proc_entity);
	comp_force_check_one(ctx->checker, proc_entity);

	DeclInfo *decl = proc_entity->decl_info;
	if (decl != nullptr && decl->proc_lit != nullptr &&
	    decl->proc_lit->kind == Ast_ProcLit) {
		Ast *body = decl->proc_lit->ProcLit.body;
		if (body != nullptr) {
			comp_ensure_callees_checked(ctx->checker, body, &visited);
		}
	}
}
