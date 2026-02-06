// Fast Backend — x86-64 instruction lowering

gb_internal void fb_low_emit_byte(fbLowCtx *ctx, u8 byte) {
	if (ctx->code_count >= ctx->code_cap) {
		u32 new_cap = ctx->code_cap * 2;
		if (new_cap < 256) new_cap = 256;
		ctx->code = gb_resize_array(heap_allocator(), ctx->code, ctx->code_cap, new_cap);
		ctx->code_cap = new_cap;
	}
	ctx->code[ctx->code_count++] = byte;
}

gb_internal void fb_low_emit_bytes(fbLowCtx *ctx, u8 const *bytes, u32 count) {
	for (u32 i = 0; i < count; i++) {
		fb_low_emit_byte(ctx, bytes[i]);
	}
}

gb_internal void fb_lower_proc_x64(fbLowCtx *ctx) {
	fbProc *p = ctx->proc;

	// Prologue: push rbp; mov rbp, rsp
	fb_low_emit_byte(ctx, 0x55);       // push rbp
	fb_low_emit_byte(ctx, 0x48);       // REX.W
	fb_low_emit_byte(ctx, 0x89);       // mov
	fb_low_emit_byte(ctx, 0xE5);       // rbp <- rsp

	// Lower each block
	for (u32 bi = 0; bi < p->block_count; bi++) {
		if (ctx->block_offsets) {
			ctx->block_offsets[bi] = ctx->code_count;
		}

		fbBlock *blk = &p->blocks[bi];
		for (u32 ii = 0; ii < blk->inst_count; ii++) {
			fbInst *inst = &p->insts[blk->first_inst + ii];
			switch (cast(fbOp)inst->op) {
			case FB_RET:
				// Epilogue: mov rsp, rbp; pop rbp; ret
				fb_low_emit_byte(ctx, 0x48);  // REX.W
				fb_low_emit_byte(ctx, 0x89);  // mov
				fb_low_emit_byte(ctx, 0xEC);  // rsp <- rbp
				fb_low_emit_byte(ctx, 0x5D);  // pop rbp
				fb_low_emit_byte(ctx, 0xC3);  // ret
				break;

			case FB_UNREACHABLE:
				fb_low_emit_byte(ctx, 0x0F);  // ud2
				fb_low_emit_byte(ctx, 0x0B);
				break;

			case FB_TRAP:
			case FB_DEBUGBREAK:
				fb_low_emit_byte(ctx, 0xCC);  // int3
				break;

			default:
				// Unimplemented opcode — emit ud2 as trap
				fb_low_emit_byte(ctx, 0x0F);
				fb_low_emit_byte(ctx, 0x0B);
				break;
			}
		}
	}
}

gb_internal void fb_lower_all(fbModule *m) {
	for_array(i, m->procs) {
		fbProc *p = m->procs[i];
		if (p->is_foreign) {
			continue;
		}

		fbLowCtx ctx = {};
		ctx.proc   = p;
		ctx.module = m;

		if (p->block_count > 0) {
			ctx.block_offsets = gb_alloc_array(heap_allocator(), u32, p->block_count);
		}

		switch (m->target.arch) {
		case FB_ARCH_X64:
			fb_lower_proc_x64(&ctx);
			break;
		default:
			GB_PANIC("fast backend: unsupported architecture for lowering");
			break;
		}

		p->machine_code_size = ctx.code_count;
		if (ctx.code_count > 0) {
			p->machine_code = gb_alloc_array(heap_allocator(), u8, ctx.code_count);
			gb_memmove(p->machine_code, ctx.code, ctx.code_count);
		}

		if (ctx.code)          gb_free(heap_allocator(), ctx.code);
		if (ctx.block_offsets) gb_free(heap_allocator(), ctx.block_offsets);
	}
}
