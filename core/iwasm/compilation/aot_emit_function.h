/*
 * Copyright (C) 2019 Intel Corporation. All rights reserved.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 */

#ifndef _AOT_EMIT_FUNCTION_H_
#define _AOT_EMIT_FUNCTION_H_

#include "aot_compiler.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Create (once) the function's return epilogue block. Exposed so the EH
   codegen in aot_emit_control.c can propagate an uncaught wasm exception to the
   caller by branching to it (the pending exception is recorded in the instance's
   cur_exception buffer, which the caller re-checks after the call). */
bool
create_func_return_block(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx);

#if WASM_ENABLE_EXCE_HANDLING != 0
bool
create_func_eh_return_block(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx);
#endif

bool
aot_compile_op_call(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                    uint32 func_idx, bool tail_call);

bool
aot_compile_op_call_indirect(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                             uint32 type_idx, uint32 tbl_idx);

bool
aot_compile_op_ref_null(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx);

bool
aot_compile_op_ref_is_null(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx);

bool
aot_compile_op_ref_func(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                        uint32 func_idx);

#if WASM_ENABLE_GC != 0
bool
aot_compile_op_call_ref(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                        uint32 type_idx, bool tail_call);
#endif

#ifdef __cplusplus
} /* end of extern "C" */
#endif

#endif /* end of _AOT_EMIT_FUNCTION_H_ */
