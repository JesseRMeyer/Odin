// Fast Backend ABI — SysV AMD64, Win64, AAPCS64 classification
//
// Phase 5: scalar classification for SysV AMD64.
// Full struct decomposition deferred to Phase 6.

// ───────────────────────────────────────────────────────────────────────
// ABI classification types
// ───────────────────────────────────────────────────────────────────────

enum fbABIClass : u8 {
	FB_ABI_INTEGER,  // passed/returned in GP register
	FB_ABI_SSE,      // passed/returned in XMM register
	FB_ABI_MEMORY,   // passed/returned on stack (by hidden pointer for returns)
	FB_ABI_IGNORE,   // zero-sized, not passed
};

struct fbABIParamInfo {
	fbABIClass classes[2];   // per-eightbyte classification
	u8         num_classes;  // 1 or 2 (2 for 9-16 byte aggregates)
	Type      *odin_type;
};

// ───────────────────────────────────────────────────────────────────────
// SysV AMD64 scalar classification
//
// Classifies Odin types into ABI classes for the SysV AMD64 calling convention.
// Phase 5 handles scalars and pointers. Struct/array decomposition is Phase 6.
// ───────────────────────────────────────────────────────────────────────

gb_internal fbABIParamInfo fb_abi_classify_type_sysv(Type *t) {
	fbABIParamInfo info = {};
	info.odin_type = t;

	if (t == nullptr) {
		info.classes[0] = FB_ABI_IGNORE;
		info.num_classes = 0;
		return info;
	}

	t = core_type(t);
	i64 sz = type_size_of(t);

	if (sz == 0) {
		info.classes[0] = FB_ABI_IGNORE;
		info.num_classes = 0;
		return info;
	}

	switch (t->kind) {
	case Type_Basic:
		switch (t->Basic.kind) {
		case Basic_f16: case Basic_f16le: case Basic_f16be:
		case Basic_f32: case Basic_f32le: case Basic_f32be:
		case Basic_f64: case Basic_f64le: case Basic_f64be:
			info.classes[0] = FB_ABI_SSE;
			info.num_classes = 1;
			return info;
		// Complex/quaternion types contain floats — MEMORY until XMM support (Phase 8)
		case Basic_complex32:
		case Basic_complex64:
		case Basic_complex128:
		case Basic_quaternion64:
		case Basic_quaternion128:
		case Basic_quaternion256:
			info.classes[0] = FB_ABI_MEMORY;
			info.num_classes = 1;
			return info;
		// String types: {ptr, int} = 16 bytes → 2 × INTEGER
		case Basic_string:
		case Basic_string16:
			info.classes[0] = FB_ABI_INTEGER;
			info.classes[1] = FB_ABI_INTEGER;
			info.num_classes = 2;
			return info;
		default:
			// All integer, boolean, and rune types
			info.classes[0] = FB_ABI_INTEGER;
			info.num_classes = 1;
			return info;
		}

	case Type_Pointer:
	case Type_MultiPointer:
	case Type_Proc:
		info.classes[0] = FB_ABI_INTEGER;
		info.num_classes = 1;
		return info;

	case Type_Enum:
		return fb_abi_classify_type_sysv(t->Enum.base_type);

	case Type_BitSet:
		info.classes[0] = FB_ABI_INTEGER;
		info.num_classes = 1;
		return info;

	// Slice and string: {rawptr, int} = 16 bytes → 2 × INTEGER
	case Type_Slice:
		info.classes[0] = FB_ABI_INTEGER;
		info.classes[1] = FB_ABI_INTEGER;
		info.num_classes = 2;
		return info;

	// Dynamic array: {rawptr, int, int, rawptr} = 32 bytes → MEMORY
	case Type_DynamicArray:
		info.classes[0] = FB_ABI_MEMORY;
		info.num_classes = 1;
		return info;

	// Map: large internal structure → MEMORY
	case Type_Map:
		info.classes[0] = FB_ABI_MEMORY;
		info.num_classes = 1;
		return info;

	default:
		// Aggregates (structs, arrays, unions, tuples, vectors, matrices):
		// MEMORY is always a safe classification. Proper field-by-field
		// decomposition (which could classify small integer-only aggregates
		// into register pairs) requires Phase 6 struct decomposition.
		info.classes[0] = FB_ABI_MEMORY;
		info.num_classes = 1;
		return info;
	}
}
