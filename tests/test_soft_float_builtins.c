// Test for lb_emit_lto_soft_float_builtins (__extendhfsf2 / __truncsfhf2)
//
// Builds the same LLVM IR as lb_emit_lto_soft_float_builtins, JITs it,
// and validates results against the reference C implementations from common.cpp.
//
// Build & run:
//   cc tests/test_soft_float_builtins.c -o test_soft_float_builtins \
//      $(llvm-config --cflags --ldflags --libs core analysis executionengine native) -lm \
//      && ./test_soft_float_builtins

#include <llvm-c/Core.h>
#include <llvm-c/Analysis.h>
#include <llvm-c/ExecutionEngine.h>
#include <llvm-c/Target.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

// ---------------------------------------------------------------------------
// Reference implementations (copied from src/common.cpp)
// ---------------------------------------------------------------------------

static float ref_f16_to_f32(uint16_t value) {
	union { uint32_t u; float f; } v, magic, inf_or_nan;
	magic.u     = (254u - 15u) << 23;
	inf_or_nan.u = (127u + 16u) << 23;
	v.u = (value & 0x7fffu) << 13;
	v.f *= magic.f;
	if (v.f >= inf_or_nan.f) {
		v.u |= 255u << 23;
	}
	v.u |= (value & 0x8000u) << 16;
	return v.f;
}

static uint16_t ref_f32_to_f16(float value) {
	union { uint32_t i; float f; } v;
	int32_t i, s, e, m;
	v.f = value;
	i = (int32_t)v.i;
	s =  (i >> 16) & 0x00008000;
	e = ((i >> 23) & 0x000000ff) - (127 - 15);
	m =   i        & 0x007fffff;

	if (e <= 0) {
		if (e < -10) return (uint16_t)s;
		m = (m | 0x00800000) >> (1 - e);
		if (m & 0x00001000)
			m += 0x00002000;
		return (uint16_t)(s | (m >> 13));
	} else if (e == 0xff - (127 - 15)) {
		if (m == 0) {
			return (uint16_t)(s | 0x7c00);
		} else {
			m >>= 13;
			return (uint16_t)(s | 0x7c00 | m | (m == 0));
		}
	} else {
		if (m & 0x00001000) {
			m += 0x00002000;
			if (m & 0x00800000) {
				m = 0;
				e += 1;
			}
		}
		if (e > 30) {
			return (uint16_t)(s | 0x7c00);
		}
		return (uint16_t)(s | (e << 10) | (m >> 13));
	}
}

// ---------------------------------------------------------------------------
// Emit the same IR as lb_emit_lto_soft_float_builtins, plus JIT-callable
// test wrappers that use i16 instead of half at the C boundary.
// ---------------------------------------------------------------------------

static void emit_builtins(LLVMModuleRef mod, LLVMContextRef ctx) {
	LLVMTypeRef i16_type  = LLVMInt16TypeInContext(ctx);
	LLVMTypeRef i32_type  = LLVMInt32TypeInContext(ctx);
	LLVMTypeRef f32_type  = LLVMFloatTypeInContext(ctx);
	LLVMTypeRef half_type = LLVMHalfTypeInContext(ctx);

	// Use half for the external ABI (matches LLVM 15+ convention)
	LLVMTypeRef h_type = half_type;

	// __extendhfsf2: half -> float
	LLVMValueRef extend_fn;
	{
		LLVMTypeRef param_types[] = { h_type };
		LLVMTypeRef fn_type = LLVMFunctionType(f32_type, param_types, 1, 0);
		extend_fn = LLVMAddFunction(mod, "__extendhfsf2", fn_type);
		LLVMSetLinkage(extend_fn, LLVMWeakAnyLinkage);

		LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(ctx, extend_fn, "entry");
		LLVMBuilderRef b = LLVMCreateBuilderInContext(ctx);
		LLVMPositionBuilderAtEnd(b, entry);

		LLVMValueRef param = LLVMGetParam(extend_fn, 0);
		LLVMValueRef value = LLVMBuildBitCast(b, param, i16_type, "to_i16");

		LLVMValueRef magic_i32 = LLVMConstInt(i32_type, (254u - 15u) << 23, 0);
		LLVMValueRef magic_f32 = LLVMBuildBitCast(b, magic_i32, f32_type, "magic");
		LLVMValueRef inf_i32 = LLVMConstInt(i32_type, (127u + 16u) << 23, 0);
		LLVMValueRef inf_f32 = LLVMBuildBitCast(b, inf_i32, f32_type, "inf_or_nan");
		LLVMValueRef val_i32 = LLVMBuildZExt(b, value, i32_type, "val_i32");
		LLVMValueRef masked = LLVMBuildAnd(b, val_i32, LLVMConstInt(i32_type, 0x7FFF, 0), "masked");
		LLVMValueRef shifted = LLVMBuildShl(b, masked, LLVMConstInt(i32_type, 13, 0), "shifted");
		LLVMValueRef v_f = LLVMBuildBitCast(b, shifted, f32_type, "v_f_raw");
		v_f = LLVMBuildFMul(b, v_f, magic_f32, "v_f");
		LLVMValueRef is_inf = LLVMBuildFCmp(b, LLVMRealOGE, v_f, inf_f32, "is_inf");
		LLVMValueRef v_u2 = LLVMBuildBitCast(b, v_f, i32_type, "v_u2");
		LLVMValueRef inf_bits = LLVMBuildOr(b, v_u2, LLVMConstInt(i32_type, 255u << 23, 0), "inf_bits");
		LLVMValueRef v_u3 = LLVMBuildSelect(b, is_inf, inf_bits, v_u2, "v_u3");
		LLVMValueRef sign = LLVMBuildAnd(b, val_i32, LLVMConstInt(i32_type, 0x8000, 0), "sign_bit");
		sign = LLVMBuildShl(b, sign, LLVMConstInt(i32_type, 16, 0), "sign");
		LLVMValueRef result_i32 = LLVMBuildOr(b, v_u3, sign, "result_i32");
		LLVMValueRef result = LLVMBuildBitCast(b, result_i32, f32_type, "result");
		LLVMBuildRet(b, result);
		LLVMDisposeBuilder(b);
	}

	// __truncsfhf2: float -> half
	LLVMValueRef trunc_fn;
	{
		LLVMTypeRef param_types[] = { f32_type };
		LLVMTypeRef fn_type = LLVMFunctionType(h_type, param_types, 1, 0);
		trunc_fn = LLVMAddFunction(mod, "__truncsfhf2", fn_type);
		LLVMSetLinkage(trunc_fn, LLVMWeakAnyLinkage);

		LLVMBasicBlockRef entry          = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "entry");
		LLVMBasicBlockRef bb_denorm      = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "denorm");
		LLVMBasicBlockRef bb_denorm_round = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "denorm_round");
		LLVMBasicBlockRef bb_denorm_end  = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "denorm_end");
		LLVMBasicBlockRef bb_tiny_ret    = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "tiny_ret");
		LLVMBasicBlockRef bb_inf_nan     = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "inf_nan");
		LLVMBasicBlockRef bb_inf         = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "inf");
		LLVMBasicBlockRef bb_inf_ret2    = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "inf_ret");
		LLVMBasicBlockRef bb_nan         = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "nan");
		LLVMBasicBlockRef bb_normal      = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "normal");
		LLVMBasicBlockRef bb_norm_round  = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "norm_round");
		LLVMBasicBlockRef bb_norm_carry  = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "norm_carry");
		LLVMBasicBlockRef bb_norm_end    = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "norm_end");
		LLVMBasicBlockRef bb_overflow    = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "overflow");
		LLVMBasicBlockRef bb_norm_done   = LLVMAppendBasicBlockInContext(ctx, trunc_fn, "norm_done");

		LLVMBuilderRef b = LLVMCreateBuilderInContext(ctx);

		LLVMPositionBuilderAtEnd(b, entry);
		LLVMValueRef value = LLVMGetParam(trunc_fn, 0);
		LLVMValueRef i = LLVMBuildBitCast(b, value, i32_type, "i");
		LLVMValueRef s = LLVMBuildLShr(b, i, LLVMConstInt(i32_type, 16, 0), "s_shift");
		s = LLVMBuildAnd(b, s, LLVMConstInt(i32_type, 0x8000, 0), "s");
		LLVMValueRef e = LLVMBuildLShr(b, i, LLVMConstInt(i32_type, 23, 0), "e_shift");
		e = LLVMBuildAnd(b, e, LLVMConstInt(i32_type, 0xFF, 0), "e_masked");
		e = LLVMBuildSub(b, e, LLVMConstInt(i32_type, 112, 0), "e");
		LLVMValueRef m = LLVMBuildAnd(b, i, LLVMConstInt(i32_type, 0x007FFFFF, 0), "m");
		LLVMValueRef e_le_0 = LLVMBuildICmp(b, LLVMIntSLE, e, LLVMConstInt(i32_type, 0, 0), "e_le_0");
		LLVMBuildCondBr(b, e_le_0, bb_denorm, bb_inf_nan);

		// Helper macro: trunc i32 to i16, then bitcast to half for return
		#define RET_HALF(val, name) do { \
			LLVMValueRef _i16 = LLVMBuildTrunc(b, (val), i16_type, (name)); \
			LLVMBuildRet(b, LLVMBuildBitCast(b, _i16, half_type, "to_half")); \
		} while(0)

		LLVMPositionBuilderAtEnd(b, bb_denorm);
		LLVMValueRef e_lt_neg10 = LLVMBuildICmp(b, LLVMIntSLT, e, LLVMConstInt(i32_type, (uint64_t)(int32_t)-10, 0), "e_lt_neg10");
		LLVMBuildCondBr(b, e_lt_neg10, bb_tiny_ret, bb_denorm_round);

		LLVMPositionBuilderAtEnd(b, bb_tiny_ret);
		RET_HALF(s, "tiny_ret_val");

		LLVMPositionBuilderAtEnd(b, bb_denorm_round);
		LLVMValueRef m_or = LLVMBuildOr(b, m, LLVMConstInt(i32_type, 0x00800000, 0), "m_or");
		LLVMValueRef shift_amt = LLVMBuildSub(b, LLVMConstInt(i32_type, 1, 0), e, "shift_amt");
		LLVMValueRef m_shifted = LLVMBuildLShr(b, m_or, shift_amt, "m_shifted");
		LLVMValueRef round_bit = LLVMBuildAnd(b, m_shifted, LLVMConstInt(i32_type, 0x1000, 0), "round_bit");
		LLVMValueRef needs_round = LLVMBuildICmp(b, LLVMIntNE, round_bit, LLVMConstInt(i32_type, 0, 0), "needs_round");
		LLVMBuildBr(b, bb_denorm_end);

		LLVMPositionBuilderAtEnd(b, bb_denorm_end);
		LLVMValueRef m_rounded = LLVMBuildAdd(b, m_shifted, LLVMConstInt(i32_type, 0x2000, 0), "m_rounded");
		LLVMValueRef m_denorm = LLVMBuildSelect(b, needs_round, m_rounded, m_shifted, "m_denorm");
		LLVMValueRef m_final_d = LLVMBuildLShr(b, m_denorm, LLVMConstInt(i32_type, 13, 0), "m_final_d");
		LLVMValueRef res_d = LLVMBuildOr(b, s, m_final_d, "res_d");
		RET_HALF(res_d, "res_d_i16");

		LLVMPositionBuilderAtEnd(b, bb_inf_nan);
		LLVMValueRef e_is_inf_nan = LLVMBuildICmp(b, LLVMIntEQ, e, LLVMConstInt(i32_type, 0xFF - 112, 0), "e_is_inf_nan");
		LLVMBuildCondBr(b, e_is_inf_nan, bb_inf, bb_normal);

		LLVMPositionBuilderAtEnd(b, bb_inf);
		LLVMValueRef m_is_zero = LLVMBuildICmp(b, LLVMIntEQ, m, LLVMConstInt(i32_type, 0, 0), "m_is_zero");
		LLVMBuildCondBr(b, m_is_zero, bb_inf_ret2, bb_nan);

		LLVMPositionBuilderAtEnd(b, bb_inf_ret2);
		RET_HALF(LLVMBuildOr(b, s, LLVMConstInt(i32_type, 0x7C00, 0), "inf_val"), "inf_ret_val");

		LLVMPositionBuilderAtEnd(b, bb_nan);
		LLVMValueRef m_nan = LLVMBuildLShr(b, m, LLVMConstInt(i32_type, 13, 0), "m_nan");
		LLVMValueRef m_nan_zero = LLVMBuildICmp(b, LLVMIntEQ, m_nan, LLVMConstInt(i32_type, 0, 0), "m_nan_zero");
		LLVMValueRef m_nan_fix = LLVMBuildSelect(b, m_nan_zero, LLVMConstInt(i32_type, 1, 0), LLVMConstInt(i32_type, 0, 0), "m_nan_fix");
		LLVMValueRef res_nan = LLVMBuildOr(b, s, LLVMConstInt(i32_type, 0x7C00, 0), "res_nan_1");
		res_nan = LLVMBuildOr(b, res_nan, m_nan, "res_nan_2");
		res_nan = LLVMBuildOr(b, res_nan, m_nan_fix, "res_nan");
		RET_HALF(res_nan, "res_nan_i16");

		LLVMPositionBuilderAtEnd(b, bb_normal);
		LLVMValueRef norm_round_bit = LLVMBuildAnd(b, m, LLVMConstInt(i32_type, 0x1000, 0), "norm_round_bit");
		LLVMValueRef norm_needs_round = LLVMBuildICmp(b, LLVMIntNE, norm_round_bit, LLVMConstInt(i32_type, 0, 0), "norm_needs_round");
		LLVMBuildCondBr(b, norm_needs_round, bb_norm_round, bb_norm_end);

		LLVMPositionBuilderAtEnd(b, bb_norm_round);
		LLVMValueRef m_plus = LLVMBuildAdd(b, m, LLVMConstInt(i32_type, 0x2000, 0), "m_plus");
		LLVMValueRef carry_bit = LLVMBuildAnd(b, m_plus, LLVMConstInt(i32_type, 0x00800000, 0), "carry_bit");
		LLVMValueRef has_carry = LLVMBuildICmp(b, LLVMIntNE, carry_bit, LLVMConstInt(i32_type, 0, 0), "has_carry");
		LLVMBuildCondBr(b, has_carry, bb_norm_carry, bb_norm_end);

		LLVMPositionBuilderAtEnd(b, bb_norm_carry);
		LLVMValueRef e_plus = LLVMBuildAdd(b, e, LLVMConstInt(i32_type, 1, 0), "e_plus");
		LLVMBuildBr(b, bb_norm_end);

		LLVMPositionBuilderAtEnd(b, bb_norm_end);
		LLVMValueRef m_phi = LLVMBuildPhi(b, i32_type, "m_phi");
		LLVMValueRef e_phi = LLVMBuildPhi(b, i32_type, "e_phi");
		{
			LLVMValueRef m_v[] = { m, m_plus, LLVMConstInt(i32_type, 0, 0) };
			LLVMBasicBlockRef m_b[] = { bb_normal, bb_norm_round, bb_norm_carry };
			LLVMAddIncoming(m_phi, m_v, m_b, 3);
			LLVMValueRef e_v[] = { e, e, e_plus };
			LLVMBasicBlockRef e_b[] = { bb_normal, bb_norm_round, bb_norm_carry };
			LLVMAddIncoming(e_phi, e_v, e_b, 3);
		}
		LLVMValueRef e_gt_30 = LLVMBuildICmp(b, LLVMIntSGT, e_phi, LLVMConstInt(i32_type, 30, 0), "e_gt_30");
		LLVMBuildCondBr(b, e_gt_30, bb_overflow, bb_norm_done);

		LLVMPositionBuilderAtEnd(b, bb_overflow);
		RET_HALF(LLVMBuildOr(b, s, LLVMConstInt(i32_type, 0x7C00, 0), "res_ovf"), "res_ovf_i16");

		LLVMPositionBuilderAtEnd(b, bb_norm_done);
		LLVMValueRef e_shifted = LLVMBuildShl(b, e_phi, LLVMConstInt(i32_type, 10, 0), "e_shifted");
		LLVMValueRef m_shifted2 = LLVMBuildLShr(b, m_phi, LLVMConstInt(i32_type, 13, 0), "m_shifted2");
		LLVMValueRef res_n = LLVMBuildOr(b, s, e_shifted, "res_n_1");
		res_n = LLVMBuildOr(b, res_n, m_shifted2, "res_n");
		RET_HALF(res_n, "res_n_i16");

		#undef RET_HALF
		LLVMDisposeBuilder(b);
	}

	// --- Test wrappers with i16 interface (callable from C via JIT) ---

	// Explicit function types for Call2 (opaque pointers in LLVM 15+)
	LLVMTypeRef extend_callee_type;
	{
		LLVMTypeRef p[] = { h_type };
		extend_callee_type = LLVMFunctionType(f32_type, p, 1, 0);
	}
	LLVMTypeRef trunc_callee_type;
	{
		LLVMTypeRef p[] = { f32_type };
		trunc_callee_type = LLVMFunctionType(h_type, p, 1, 0);
	}

	// test_extend(i16) -> float: bitcasts i16 to half, calls __extendhfsf2
	{
		LLVMTypeRef param_types[] = { i16_type };
		LLVMTypeRef fn_type = LLVMFunctionType(f32_type, param_types, 1, 0);
		LLVMValueRef fn = LLVMAddFunction(mod, "test_extend", fn_type);

		LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(ctx, fn, "entry");
		LLVMBuilderRef b = LLVMCreateBuilderInContext(ctx);
		LLVMPositionBuilderAtEnd(b, entry);

		LLVMValueRef arg = LLVMGetParam(fn, 0);
		LLVMValueRef as_half = LLVMBuildBitCast(b, arg, half_type, "as_half");
		LLVMValueRef args[] = { as_half };
		LLVMValueRef result = LLVMBuildCall2(b, extend_callee_type, extend_fn, args, 1, "result");
		LLVMBuildRet(b, result);
		LLVMDisposeBuilder(b);
	}

	// test_trunc(float) -> i16: calls __truncsfhf2, bitcasts half result to i16
	{
		LLVMTypeRef param_types[] = { f32_type };
		LLVMTypeRef fn_type = LLVMFunctionType(i16_type, param_types, 1, 0);
		LLVMValueRef fn = LLVMAddFunction(mod, "test_trunc", fn_type);

		LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(ctx, fn, "entry");
		LLVMBuilderRef b = LLVMCreateBuilderInContext(ctx);
		LLVMPositionBuilderAtEnd(b, entry);

		LLVMValueRef arg = LLVMGetParam(fn, 0);
		LLVMValueRef args[] = { arg };
		LLVMValueRef half_result = LLVMBuildCall2(b, trunc_callee_type, trunc_fn, args, 1, "half_result");
		LLVMValueRef as_i16 = LLVMBuildBitCast(b, half_result, i16_type, "as_i16");
		LLVMBuildRet(b, as_i16);
		LLVMDisposeBuilder(b);
	}
}

// ---------------------------------------------------------------------------
// Test harness
// ---------------------------------------------------------------------------

static uint32_t float_bits(float f) {
	uint32_t u; memcpy(&u, &f, 4); return u;
}

static float bits_float(uint32_t u) {
	float f; memcpy(&f, &u, 4); return f;
}

int main(void) {
	LLVMLinkInMCJIT();
	LLVMInitializeNativeTarget();
	LLVMInitializeNativeAsmPrinter();

	LLVMContextRef ctx = LLVMContextCreate();
	LLVMModuleRef mod = LLVMModuleCreateWithNameInContext("test_soft_float", ctx);

	emit_builtins(mod, ctx);

	// Verify module
	char *error = NULL;
	if (LLVMVerifyModule(mod, LLVMReturnStatusAction, &error)) {
		fprintf(stderr, "FAIL: Module verification:\n%s\n", error);
		LLVMDisposeMessage(error);
		return 1;
	}
	LLVMDisposeMessage(error);
	printf("OK   module verification\n");

	// Create JIT
	LLVMExecutionEngineRef ee;
	error = NULL;
	if (LLVMCreateExecutionEngineForModule(&ee, mod, &error)) {
		fprintf(stderr, "FAIL: JIT creation: %s\n", error);
		LLVMDisposeMessage(error);
		return 1;
	}

	typedef float    (*extend_fn_t)(uint16_t);
	typedef uint16_t (*trunc_fn_t)(float);

	// Use the test wrappers which have i16-based C calling convention
	extend_fn_t jit_extend = (extend_fn_t)(uintptr_t)LLVMGetFunctionAddress(ee, "test_extend");
	trunc_fn_t  jit_trunc  = (trunc_fn_t)(uintptr_t)LLVMGetFunctionAddress(ee, "test_trunc");

	if (!jit_extend || !jit_trunc) {
		fprintf(stderr, "FAIL: could not resolve JIT symbols\n");
		return 1;
	}

	int failures = 0;
	int tests = 0;

	// --- Test __extendhfsf2 (f16 -> f32) ---
	// Test every possible f16 bit pattern (only 65536 of them)
	for (uint32_t h = 0; h < 0x10000; h++) {
		uint16_t h16 = (uint16_t)h;
		float expected = ref_f16_to_f32(h16);
		float got      = jit_extend(h16);

		uint32_t exp_bits = float_bits(expected);
		uint32_t got_bits = float_bits(got);

		if (exp_bits != got_bits) {
			if (failures < 20) {
				fprintf(stderr, "FAIL extend 0x%04X: expected 0x%08X, got 0x%08X\n",
					h16, exp_bits, got_bits);
			}
			failures++;
		}
		tests++;
	}
	printf("%s   __extendhfsf2: %d/%d passed\n",
		(failures == 0) ? "OK  " : "FAIL", tests - failures, tests);

	// --- Test __truncsfhf2 (f32 -> f16) ---
	struct { float f; const char *desc; } trunc_tests[] = {
		{ 0.0f,  "+0" },
		{ -0.0f, "-0" },
		{ 1.0f,   "1.0" },
		{ -1.0f,  "-1.0" },
		{ 0.5f,   "0.5" },
		{ -0.5f,  "-0.5" },
		{ 2.0f,   "2.0" },
		{ 65504.0f, "max normal f16" },
		{ -65504.0f, "-max normal f16" },
		{ 0.00006103515625f, "min normal f16" },
		{ 5.96046448e-08f, "min subnormal f16" },
		{ 0.000060975552f, "max subnormal f16" },
		{ 100000.0f, "overflow to inf" },
		{ -100000.0f, "overflow to -inf" },
		{ INFINITY,  "+inf" },
		{ -INFINITY, "-inf" },
		{ 1e-10f,  "tiny positive" },
		{ -1e-10f, "tiny negative" },
		{ 1.0009765625f, "round-down boundary" },
		{ 1.0019531250f, "round-up boundary" },
		{ 0.333333f, "1/3" },
		{ 3.14159f, "pi" },
		{ -3.14159f, "-pi" },
	};

	int trunc_failures = 0;
	int n_trunc_structured = (int)(sizeof(trunc_tests) / sizeof(trunc_tests[0]));

	for (int i = 0; i < n_trunc_structured; i++) {
		float f = trunc_tests[i].f;
		uint16_t expected = ref_f32_to_f16(f);
		uint16_t got      = jit_trunc(f);
		if (expected != got) {
			fprintf(stderr, "FAIL trunc %s (0x%08X): expected 0x%04X, got 0x%04X\n",
				trunc_tests[i].desc, float_bits(f), expected, got);
			trunc_failures++;
		}
	}

	// NaN tests
	{
		float nan_val = bits_float(0x7FC00000);
		uint16_t expected = ref_f32_to_f16(nan_val);
		uint16_t got      = jit_trunc(nan_val);
		if (expected != got) {
			fprintf(stderr, "FAIL trunc qNaN: expected 0x%04X, got 0x%04X\n", expected, got);
			trunc_failures++;
		}

		float snan_val = bits_float(0x7F800001);
		expected = ref_f32_to_f16(snan_val);
		got      = jit_trunc(snan_val);
		if (expected != got) {
			fprintf(stderr, "FAIL trunc sNaN: expected 0x%04X, got 0x%04X\n", expected, got);
			trunc_failures++;
		}
	}

	// Exhaustive round-trip: for every non-NaN f16 value, trunc(extend(h)) == h
	int roundtrip_failures = 0;
	for (uint32_t h = 0; h < 0x10000; h++) {
		uint16_t h16 = (uint16_t)h;
		if ((h16 & 0x7C00) == 0x7C00 && (h16 & 0x03FF) != 0) continue;

		float f = jit_extend(h16);
		uint16_t back = jit_trunc(f);
		if (back != h16) {
			if (roundtrip_failures < 10) {
				fprintf(stderr, "FAIL roundtrip 0x%04X -> %g -> 0x%04X\n", h16, f, back);
			}
			roundtrip_failures++;
		}
	}

	printf("%s   __truncsfhf2: %d structured, %d roundtrip failures\n",
		(trunc_failures == 0 && roundtrip_failures == 0) ? "OK  " : "FAIL",
		trunc_failures, roundtrip_failures);

	int total_failures = failures + trunc_failures + roundtrip_failures;
	printf("\n%s\n", total_failures == 0 ? "ALL TESTS PASSED" : "SOME TESTS FAILED");

	LLVMDisposeExecutionEngine(ee);
	LLVMContextDispose(ctx);

	return total_failures != 0;
}
