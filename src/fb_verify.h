// Fast Backend Verification — macros, opcode specification table
//
// Three layers:
//   Layer 1: FB_VERIFY / FB_VERIFY_MSG — inline pre/postconditions (crash hard, bypass recovery)
//   Layer 2: fb_verify_proc / fb_verify_module — structural sweeps between phases
//   Layer 3: fb_verify_regalloc — register allocator bidirectional consistency
//
// FB_VERIFY clears fb_recovery_active before trapping so SIGILL propagates
// to the default handler → core dump. This distinguishes compiler bugs (hard crash)
// from unimplemented features (recovery to stub, via existing GB_PANIC).

#define FB_VERIFY(cond) do { if (!(cond)) { \
	gb_assert_handler("FB_VERIFY", #cond, __FILE__, cast(i64)__LINE__, NULL); \
	fb_recovery_active = false; \
	GB_DEBUG_TRAP(); \
} } while(0)

#define FB_VERIFY_MSG(cond, msg, ...) do { if (!(cond)) { \
	gb_assert_handler("FB_VERIFY", #cond, __FILE__, cast(i64)__LINE__, msg, ##__VA_ARGS__); \
	fb_recovery_active = false; \
	GB_DEBUG_TRAP(); \
} } while(0)

// ───────────────────────────────────────────────────────────────────────
// Opcode operand role specification
// ───────────────────────────────────────────────────────────────────────

enum fbOperandRole : u8 {
	FBO_NONE,       // must be FB_NOREG
	FBO_VALUE,      // SSA value ID, must be < next_value
	FBO_VALUE_OPT,  // value ID or FB_NOREG (e.g., RET void)
	FBO_BLOCK,      // block ID, must be < block_count
	FBO_SLOT,       // slot index, must be < slot_count
	FBO_AUX,        // aux pool index, must be < aux_count
	FBO_COUNT,      // raw count (no range constraint)
};

struct fbOpSpec {
	fbOperandRole a, b, c;
	bool has_result;
	bool is_terminator;
};

// Indexed by fbOp. Verified against both builder (fb_build.cpp) and lowerer (fb_lower_x64.cpp).
gb_global const fbOpSpec fb_op_specs[FB_OP_COUNT] = {
	// Constants: ICONST, FCONST, SYMADDR, UNDEF
	[FB_ICONST]    = { FBO_NONE,      FBO_NONE,  FBO_NONE,  true,  false },
	[FB_FCONST]    = { FBO_NONE,      FBO_NONE,  FBO_NONE,  true,  false },
	[FB_SYMADDR]   = { FBO_NONE,      FBO_NONE,  FBO_NONE,  true,  false },
	[FB_UNDEF]     = { FBO_NONE,      FBO_NONE,  FBO_NONE,  true,  false },

	// Stack
	[FB_ALLOCA]    = { FBO_SLOT,      FBO_NONE,  FBO_NONE,  true,  false },

	// Memory
	[FB_LOAD]      = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_STORE]     = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  false, false },
	[FB_MEMCPY]    = { FBO_VALUE,     FBO_VALUE, FBO_VALUE, false, false },
	[FB_MEMSET]    = { FBO_VALUE,     FBO_VALUE, FBO_VALUE, false, false },
	[FB_MEMZERO]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  false, false },

	// Pointer arithmetic
	[FB_MEMBER]    = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_ARRAY]     = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_PTR2INT]   = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_INT2PTR]   = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },

	// Integer arithmetic (binary)
	[FB_ADD]       = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_SUB]       = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_MUL]       = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_SDIV]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_UDIV]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_SMOD]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_UMOD]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_NEG]       = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },

	// Bitwise
	[FB_AND]       = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_OR]        = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_XOR]       = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_NOT]       = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_SHL]       = { FBO_VALUE,     FBO_VALUE_OPT, FBO_NONE,  true,  false }, // SIMD constant shift: b=FB_NOREG, amount in imm
	[FB_LSHR]      = { FBO_VALUE,     FBO_VALUE_OPT, FBO_NONE,  true,  false },
	[FB_ASHR]      = { FBO_VALUE,     FBO_VALUE_OPT, FBO_NONE,  true,  false },
	[FB_ROL]       = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_ROR]       = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },

	// Float arithmetic
	[FB_FADD]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_FSUB]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_FMUL]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_FDIV]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_FNEG]      = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_FABS]      = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_SQRT]      = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_FMIN]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_FMAX]      = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },

	// Comparisons
	[FB_CMP_EQ]    = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_NE]    = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_SLT]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_SLE]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_SGT]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_SGE]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_ULT]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_ULE]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_UGT]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_UGE]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_FEQ]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_FNE]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_FLT]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_FLE]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_FGT]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_CMP_FGE]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },

	// Conversions
	[FB_SEXT]      = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_ZEXT]      = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_TRUNC]     = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_FPEXT]     = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_FPTRUNC]   = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_SI2FP]     = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_UI2FP]     = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_FP2SI]     = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_FP2UI]     = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_BITCAST]   = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },

	// Select
	[FB_SELECT]    = { FBO_VALUE,     FBO_VALUE, FBO_VALUE, true,  false },

	// Control flow
	[FB_JUMP]      = { FBO_BLOCK,     FBO_NONE,  FBO_NONE,  false, true },
	[FB_BRANCH]    = { FBO_VALUE,     FBO_BLOCK, FBO_BLOCK, false, true },
	// c is FBO_COUNT because zero-case switches set c=aux_count. Aux bounds validated in SWITCH-specific check.
	[FB_SWITCH]    = { FBO_VALUE,     FBO_BLOCK, FBO_COUNT, false, true },
	[FB_RET]       = { FBO_VALUE_OPT, FBO_NONE,  FBO_NONE,  false, true },
	[FB_UNREACHABLE] = { FBO_NONE,    FBO_NONE,  FBO_NONE,  false, true },
	[FB_TRAP]      = { FBO_NONE,      FBO_NONE,  FBO_NONE,  false, true },
	[FB_DEBUGBREAK] = { FBO_NONE,     FBO_NONE,  FBO_NONE,  false, true },

	// Function calls: a=target, b=aux_start, c=arg_count
	// b is FBO_COUNT (not FBO_AUX) because zero-arg calls set b=aux_count (one-past-end).
	// Aux bounds are validated in the CALL-specific check in fb_verify_proc.
	[FB_CALL]      = { FBO_VALUE,     FBO_COUNT, FBO_COUNT, true,  false },
	[FB_TAILCALL]  = { FBO_VALUE,     FBO_COUNT, FBO_COUNT, false, true },

	// Multi-value projection
	[FB_PROJ]      = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },

	// Atomics
	[FB_ATOMIC_LOAD]  = { FBO_VALUE,  FBO_NONE,  FBO_NONE,  true,  false },
	[FB_ATOMIC_STORE] = { FBO_VALUE,  FBO_VALUE, FBO_NONE,  false, false },
	[FB_ATOMIC_XCHG]  = { FBO_VALUE,  FBO_VALUE, FBO_NONE,  true,  false },
	[FB_ATOMIC_ADD]   = { FBO_VALUE,  FBO_VALUE, FBO_NONE,  true,  false },
	[FB_ATOMIC_SUB]   = { FBO_VALUE,  FBO_VALUE, FBO_NONE,  true,  false },
	[FB_ATOMIC_AND]   = { FBO_VALUE,  FBO_VALUE, FBO_NONE,  true,  false },
	[FB_ATOMIC_OR]    = { FBO_VALUE,  FBO_VALUE, FBO_NONE,  true,  false },
	[FB_ATOMIC_XOR]   = { FBO_VALUE,  FBO_VALUE, FBO_NONE,  true,  false },
	[FB_ATOMIC_CAS]   = { FBO_VALUE,  FBO_VALUE, FBO_VALUE, true,  false },
	[FB_FENCE]        = { FBO_NONE,   FBO_NONE,  FBO_NONE,  false, false },

	// Bit manipulation
	[FB_BSWAP]     = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_CLZ]       = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_CTZ]       = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_POPCNT]    = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },

	// Wide arithmetic
	[FB_ADDPAIR]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_MULPAIR]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },

	// Vector (SIMD)
	[FB_VSHUFFLE]  = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_VEXTRACT]  = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },
	[FB_VINSERT]   = { FBO_VALUE,     FBO_VALUE, FBO_NONE,  true,  false },
	[FB_VSPLAT]    = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  true,  false },

	// Miscellaneous
	[FB_VA_START]  = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  false, false },
	[FB_PREFETCH]  = { FBO_VALUE,     FBO_NONE,  FBO_NONE,  false, false },
	[FB_CYCLE]     = { FBO_NONE,      FBO_NONE,  FBO_NONE,  true,  false },
	// ASM encoding: a=aux_start, b=arg_count, c=unused(0), imm=variant
	[FB_ASM]       = { FBO_COUNT,     FBO_COUNT,     FBO_COUNT, true, false },

	// SSA
	[FB_PHI]       = { FBO_NONE,      FBO_NONE,  FBO_NONE,  true,  false },
};

// ───────────────────────────────────────────────────────────────────────
// Opcode name table (for diagnostic messages)
// ───────────────────────────────────────────────────────────────────────

gb_global const char *fb_op_names[FB_OP_COUNT] = {
	[FB_ICONST] = "ICONST", [FB_FCONST] = "FCONST", [FB_SYMADDR] = "SYMADDR", [FB_UNDEF] = "UNDEF",
	[FB_ALLOCA] = "ALLOCA",
	[FB_LOAD] = "LOAD", [FB_STORE] = "STORE", [FB_MEMCPY] = "MEMCPY", [FB_MEMSET] = "MEMSET", [FB_MEMZERO] = "MEMZERO",
	[FB_MEMBER] = "MEMBER", [FB_ARRAY] = "ARRAY", [FB_PTR2INT] = "PTR2INT", [FB_INT2PTR] = "INT2PTR",
	[FB_ADD] = "ADD", [FB_SUB] = "SUB", [FB_MUL] = "MUL", [FB_SDIV] = "SDIV", [FB_UDIV] = "UDIV",
	[FB_SMOD] = "SMOD", [FB_UMOD] = "UMOD", [FB_NEG] = "NEG",
	[FB_AND] = "AND", [FB_OR] = "OR", [FB_XOR] = "XOR", [FB_NOT] = "NOT",
	[FB_SHL] = "SHL", [FB_LSHR] = "LSHR", [FB_ASHR] = "ASHR", [FB_ROL] = "ROL", [FB_ROR] = "ROR",
	[FB_FADD] = "FADD", [FB_FSUB] = "FSUB", [FB_FMUL] = "FMUL", [FB_FDIV] = "FDIV",
	[FB_FNEG] = "FNEG", [FB_FABS] = "FABS", [FB_SQRT] = "SQRT", [FB_FMIN] = "FMIN", [FB_FMAX] = "FMAX",
	[FB_CMP_EQ] = "CMP_EQ", [FB_CMP_NE] = "CMP_NE",
	[FB_CMP_SLT] = "CMP_SLT", [FB_CMP_SLE] = "CMP_SLE", [FB_CMP_SGT] = "CMP_SGT", [FB_CMP_SGE] = "CMP_SGE",
	[FB_CMP_ULT] = "CMP_ULT", [FB_CMP_ULE] = "CMP_ULE", [FB_CMP_UGT] = "CMP_UGT", [FB_CMP_UGE] = "CMP_UGE",
	[FB_CMP_FEQ] = "CMP_FEQ", [FB_CMP_FNE] = "CMP_FNE",
	[FB_CMP_FLT] = "CMP_FLT", [FB_CMP_FLE] = "CMP_FLE", [FB_CMP_FGT] = "CMP_FGT", [FB_CMP_FGE] = "CMP_FGE",
	[FB_SEXT] = "SEXT", [FB_ZEXT] = "ZEXT", [FB_TRUNC] = "TRUNC",
	[FB_FPEXT] = "FPEXT", [FB_FPTRUNC] = "FPTRUNC",
	[FB_SI2FP] = "SI2FP", [FB_UI2FP] = "UI2FP", [FB_FP2SI] = "FP2SI", [FB_FP2UI] = "FP2UI",
	[FB_BITCAST] = "BITCAST",
	[FB_SELECT] = "SELECT",
	[FB_JUMP] = "JUMP", [FB_BRANCH] = "BRANCH", [FB_SWITCH] = "SWITCH", [FB_RET] = "RET",
	[FB_UNREACHABLE] = "UNREACHABLE", [FB_TRAP] = "TRAP", [FB_DEBUGBREAK] = "DEBUGBREAK",
	[FB_CALL] = "CALL", [FB_TAILCALL] = "TAILCALL",
	[FB_PROJ] = "PROJ",
	[FB_ATOMIC_LOAD] = "ATOMIC_LOAD", [FB_ATOMIC_STORE] = "ATOMIC_STORE",
	[FB_ATOMIC_XCHG] = "ATOMIC_XCHG", [FB_ATOMIC_ADD] = "ATOMIC_ADD",
	[FB_ATOMIC_SUB] = "ATOMIC_SUB", [FB_ATOMIC_AND] = "ATOMIC_AND",
	[FB_ATOMIC_OR] = "ATOMIC_OR", [FB_ATOMIC_XOR] = "ATOMIC_XOR",
	[FB_ATOMIC_CAS] = "ATOMIC_CAS", [FB_FENCE] = "FENCE",
	[FB_BSWAP] = "BSWAP", [FB_CLZ] = "CLZ", [FB_CTZ] = "CTZ", [FB_POPCNT] = "POPCNT",
	[FB_ADDPAIR] = "ADDPAIR", [FB_MULPAIR] = "MULPAIR",
	[FB_VSHUFFLE] = "VSHUFFLE", [FB_VEXTRACT] = "VEXTRACT", [FB_VINSERT] = "VINSERT", [FB_VSPLAT] = "VSPLAT",
	[FB_VA_START] = "VA_START", [FB_PREFETCH] = "PREFETCH", [FB_CYCLE] = "CYCLE", [FB_ASM] = "ASM",
	[FB_PHI] = "PHI",
};

// ───────────────────────────────────────────────────────────────────────
// Forward declarations
// ───────────────────────────────────────────────────────────────────────

gb_internal void fb_verify_proc(fbProc *p);
gb_internal void fb_verify_module(fbModule *m);
gb_internal void fb_verify_regalloc(fbLowCtx *ctx);
