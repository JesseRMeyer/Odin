// Software implementations of __extendhfsf2 (f16->f32) and __truncsfhf2 (f32->f16).
// Linked when LTO is enabled on targets without native f16 support.
//
// Compile for Windows x86-64:
//   clang -c -O2 --target=x86_64-windows-msvc -o bin/llvm/windows/soft_float.obj src/soft_float.c

#include <stdint.h>

#ifdef __clang__
#if __clang_major__ >= 15
#define HAS_FLOAT16 1
#endif
#endif

#ifdef HAS_FLOAT16
typedef _Float16 f16;
#else
typedef uint16_t f16;
#endif

static uint16_t to_u16(f16 v) {
	uint16_t u;
#ifdef HAS_FLOAT16
	__builtin_memcpy(&u, &v, 2);
#else
	u = v;
#endif
	return u;
}

static f16 from_u16(uint16_t u) {
	f16 v;
#ifdef HAS_FLOAT16
	__builtin_memcpy(&v, &u, 2);
#else
	v = u;
#endif
	return v;
}

__attribute__((weak)) float __extendhfsf2(f16 param) {
	typedef union { uint32_t u; float f; } fp32;

	uint16_t value = to_u16(param);

	fp32 magic     = { (254u - 15u) << 23 };
	fp32 inf_or_nan = { (127u + 16u) << 23 };
	fp32 v;

	v.u = (value & 0x7FFFu) << 13;
	v.f *= magic.f;
	if (v.f >= inf_or_nan.f) {
		v.u |= 255u << 23;
	}
	v.u |= (value & 0x8000u) << 16;
	return v.f;
}

__attribute__((weak)) f16 __truncsfhf2(float value) {
	typedef union { uint32_t i; float f; } fp32;

	fp32 v;
	v.f = value;

	int32_t i = (int32_t)v.i;
	int32_t s = (i >> 16) & 0x00008000;
	int32_t e = ((i >> 23) & 0x000000FF) - (127 - 15);
	int32_t m = i & 0x007FFFFF;

	if (e <= 0) {
		if (e < -10) return from_u16((uint16_t)s);
		m = (m | 0x00800000) >> (1 - e);
		if (m & 0x00001000)
			m += 0x00002000;
		return from_u16((uint16_t)(s | (m >> 13)));
	} else if (e == 0xFF - (127 - 15)) {
		if (m == 0) {
			return from_u16((uint16_t)(s | 0x7C00));
		} else {
			m >>= 13;
			return from_u16((uint16_t)(s | 0x7C00 | m | (m == 0)));
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
			return from_u16((uint16_t)(s | 0x7C00));
		}
		return from_u16((uint16_t)(s | (e << 10) | (m >> 13)));
	}
}
