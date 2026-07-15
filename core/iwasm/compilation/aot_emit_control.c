/*
 * Copyright (C) 2019 Intel Corporation. All rights reserved.
 * SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
 */

#include "aot_emit_control.h"
#include "aot_compiler.h"
#include "aot_emit_exception.h"
#include "aot_stack_frame_comp.h"
#if WASM_ENABLE_GC != 0
#include "aot_emit_gc.h"
#endif
#include "../aot/aot_runtime.h"
#include "../interpreter/wasm_loader.h"
#include "../interpreter/wasm_opcode.h"
#include "../common/wasm_loader_common.h"

#if WASM_ENABLE_DEBUG_AOT != 0
#include "debug/dwarf_extractor.h"
#endif

static char *block_name_prefix[] = { "block", "loop", "if" };
static char *block_name_suffix[] = { "begin", "else", "end" };

/* clang-format off */
enum {
    LABEL_BEGIN = 0,
    LABEL_ELSE,
    LABEL_END
};
/* clang-format on */

static void
format_block_name(char *name, uint32 name_size, uint32 block_index,
                  uint32 label_type, uint32 label_id)
{
    if (label_type != LABEL_TYPE_FUNCTION)
        snprintf(name, name_size, "%s%d%s%s", block_name_prefix[label_type],
                 block_index, "_", block_name_suffix[label_id]);
    else
        snprintf(name, name_size, "%s", "func_end");
}

#define CREATE_BLOCK(new_llvm_block, name)                                   \
    do {                                                                     \
        if (!(new_llvm_block = LLVMAppendBasicBlockInContext(                \
                  comp_ctx->context, func_ctx->func, name))) {               \
            aot_set_last_error("add LLVM basic block failed.");              \
            goto fail;                                                       \
        }                                                                    \
        if (!strcmp(name, "func_end") && comp_ctx->aux_stack_frame_type      \
            && comp_ctx->call_stack_features.frame_per_function) {           \
            LLVMBasicBlockRef cur_block =                                    \
                LLVMGetInsertBlock(comp_ctx->builder);                       \
            SET_BUILDER_POS(new_llvm_block);                                 \
            if (!aot_free_frame_per_function_frame_for_aot_func(comp_ctx,    \
                                                                func_ctx)) { \
                goto fail;                                                   \
            }                                                                \
            SET_BUILDER_POS(cur_block);                                      \
        }                                                                    \
    } while (0)

#define CURR_BLOCK() LLVMGetInsertBlock(comp_ctx->builder)

#define MOVE_BLOCK_AFTER(llvm_block, llvm_block_after) \
    LLVMMoveBasicBlockAfter(llvm_block, llvm_block_after)

#define MOVE_BLOCK_AFTER_CURR(llvm_block) \
    LLVMMoveBasicBlockAfter(llvm_block, CURR_BLOCK())

#define MOVE_BLOCK_BEFORE(llvm_block, llvm_block_before) \
    LLVMMoveBasicBlockBefore(llvm_block, llvm_block_before)

#define BUILD_BR(llvm_block)                               \
    do {                                                   \
        if (!LLVMBuildBr(comp_ctx->builder, llvm_block)) { \
            aot_set_last_error("llvm build br failed.");   \
            goto fail;                                     \
        }                                                  \
    } while (0)

#define BUILD_COND_BR(value_if, block_then, block_else)               \
    do {                                                              \
        if (!LLVMBuildCondBr(comp_ctx->builder, value_if, block_then, \
                             block_else)) {                           \
            aot_set_last_error("llvm build cond br failed.");         \
            goto fail;                                                \
        }                                                             \
    } while (0)

#define BUILD_COND_BR_V(value_if, block_then, block_else, instr)               \
    do {                                                                       \
        if (!(instr = LLVMBuildCondBr(comp_ctx->builder, value_if, block_then, \
                                      block_else))) {                          \
            aot_set_last_error("llvm build cond br failed.");                  \
            goto fail;                                                         \
        }                                                                      \
    } while (0)

#define SET_BUILDER_POS(llvm_block) \
    LLVMPositionBuilderAtEnd(comp_ctx->builder, llvm_block)

#define CREATE_RESULT_VALUE_PHIS(block)                                     \
    do {                                                                    \
        if (block->result_count && !block->result_phis) {                   \
            uint32 _i;                                                      \
            uint64 _size;                                                   \
            LLVMBasicBlockRef _block_curr = CURR_BLOCK();                   \
            /* Allocate memory */                                           \
            _size = sizeof(LLVMValueRef) * (uint64)block->result_count;     \
            if (_size >= UINT32_MAX                                         \
                || !(block->result_phis =                                   \
                         wasm_runtime_malloc((uint32)_size))) {             \
                aot_set_last_error("allocate memory failed.");              \
                goto fail;                                                  \
            }                                                               \
            SET_BUILDER_POS(block->llvm_end_block);                         \
            LLVMValueRef first_instr =                                      \
                get_first_non_phi(block->llvm_end_block);                   \
            if (first_instr) {                                              \
                LLVMPositionBuilderBefore(comp_ctx->builder, first_instr);  \
            }                                                               \
            for (_i = 0; _i < block->result_count; _i++) {                  \
                if (!(block->result_phis[_i] = LLVMBuildPhi(                \
                          comp_ctx->builder,                                \
                          TO_LLVM_TYPE(block->result_types[_i]), "phi"))) { \
                    aot_set_last_error("llvm build phi failed.");           \
                    goto fail;                                              \
                }                                                           \
            }                                                               \
            SET_BUILDER_POS(_block_curr);                                   \
        }                                                                   \
    } while (0)

#define ADD_TO_RESULT_PHIS(block, value, idx)                                  \
    do {                                                                       \
        LLVMBasicBlockRef _block_curr = CURR_BLOCK();                          \
        LLVMTypeRef phi_ty = LLVMTypeOf(block->result_phis[idx]);              \
        LLVMTypeRef value_ty = LLVMTypeOf(value);                              \
        bh_assert(LLVMGetTypeKind(phi_ty) == LLVMGetTypeKind(value_ty));       \
        bh_assert(LLVMGetTypeContext(phi_ty) == LLVMGetTypeContext(value_ty)); \
        LLVMAddIncoming(block->result_phis[idx], &value, &_block_curr, 1);     \
        (void)phi_ty;                                                          \
        (void)value_ty;                                                        \
    } while (0)

#define BUILD_ICMP(op, left, right, res, name)                                \
    do {                                                                      \
        if (!(res =                                                           \
                  LLVMBuildICmp(comp_ctx->builder, op, left, right, name))) { \
            aot_set_last_error("llvm build icmp failed.");                    \
            goto fail;                                                        \
        }                                                                     \
    } while (0)

#define ADD_TO_PARAM_PHIS(block, value, idx)                              \
    do {                                                                  \
        LLVMBasicBlockRef _block_curr = CURR_BLOCK();                     \
        LLVMAddIncoming(block->param_phis[idx], &value, &_block_curr, 1); \
    } while (0)

static LLVMBasicBlockRef
find_next_llvm_end_block(AOTBlock *block)
{
    block = block->prev;
    while (block && !block->llvm_end_block)
        block = block->prev;
    return block ? block->llvm_end_block : NULL;
}

static AOTBlock *
get_target_block(AOTFuncContext *func_ctx, uint32 br_depth)
{
    uint32 i = br_depth;
    AOTBlock *block = func_ctx->block_stack.block_list_end;

    while (i-- > 0 && block) {
        block = block->prev;
    }

    if (!block) {
        aot_set_last_error("WASM block stack underflow.");
        return NULL;
    }
    return block;
}

LLVMValueRef
get_first_non_phi(LLVMBasicBlockRef block)
{
    LLVMValueRef instr = LLVMGetFirstInstruction(block);

    while (instr && LLVMIsAPHINode(instr)) {
        instr = LLVMGetNextInstruction(instr);
    }

    return instr;
}

static void
clear_frame_locals(AOTCompFrame *aot_frame)
{
    uint32 i;

    for (i = 0; i < aot_frame->max_local_cell_num; i++) {
        aot_frame->lp[i].dirty = 0;
        aot_frame->lp[i].value = NULL;
        if (aot_frame->comp_ctx->enable_gc)
            /* Mark the ref flag as committed */
            aot_frame->lp[i].committed_ref = aot_frame->lp[i].ref + 1;
    }
}

static void
restore_frame_sp_for_op_else(AOTBlock *block, AOTCompFrame *aot_frame)
{
    uint32 all_cell_num =
        aot_frame->max_local_cell_num + aot_frame->max_stack_cell_num;
    AOTValueSlot *p_end = aot_frame->lp + all_cell_num, *p;

    /* Reset all the value slots from current frame sp for the else
       branch since they be the same as starting to translate the
       if branch */
    for (p = block->frame_sp_begin; p < p_end; p++) {
        p->dirty = 0;
        p->value = NULL;
        p->type = 0;
        if (aot_frame->comp_ctx->enable_gc) {
            p->ref = 0;
            p->committed_ref = 1;
        }
    }

    bh_assert(aot_frame->sp >= block->frame_sp_begin);
    aot_frame->sp = block->frame_sp_begin;
}

static void
restore_frame_sp_for_op_end(AOTBlock *block, AOTCompFrame *aot_frame)
{
    uint32 all_cell_num =
        aot_frame->max_local_cell_num + aot_frame->max_stack_cell_num;
    AOTValueSlot *p_end = aot_frame->lp + all_cell_num, *p;

    bh_assert(block->frame_sp_max_reached >= block->frame_sp_begin);

    /* Reset all the value slots from current frame sp to be same as
       starting to translate this block, except for the frame ref
       flags: set the flags to uncommitted before the max frame sp
       ever reached, set the flags to committed non-ref after that */
    for (p = block->frame_sp_begin; p < p_end; p++) {
        p->dirty = 0;
        p->value = NULL;
        p->type = 0;
        if (aot_frame->comp_ctx->enable_gc) {
            p->ref = 0;
            if (p < block->frame_sp_max_reached)
                p->committed_ref = 0;
            else
                p->committed_ref = 1;
        }
    }

    bh_assert(aot_frame->sp >= block->frame_sp_begin);
    aot_frame->sp = block->frame_sp_begin;
}

#if WASM_ENABLE_BRANCH_HINTS != 0
static void
aot_emit_branch_hint(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                     uint32 offset, LLVMValueRef br_if_instr)
{
    struct WASMCompilationHint *hint = func_ctx->function_hints;
    while (hint != NULL) {
        if (hint->type == WASM_COMPILATION_BRANCH_HINT
            && ((struct WASMCompilationHintBranchHint *)hint)->offset
                   == offset) {
            break;
        }
        hint = hint->next;
    }
    if (hint != NULL) {
        // same weight llvm MDBuilder::createLikelyBranchWeights assigns
        const uint32_t likely_weight = (1U << 20) - 1;
        const uint32_t unlikely_weight = 1;
        aot_set_cond_br_weights(
            comp_ctx, br_if_instr,
            ((struct WASMCompilationHintBranchHint *)hint)->is_likely
                ? likely_weight
                : unlikely_weight,
            ((struct WASMCompilationHintBranchHint *)hint)->is_likely
                ? unlikely_weight
                : likely_weight);
    }
}
#endif

#if WASM_ENABLE_EXCE_HANDLING != 0
/* Finalize a try's last-catch mismatch edge (its `catch_next` block): an
   exception matched by no catch of this try re-propagates to the enclosing
   try's catch-dispatch, or -- with no enclosing try -- the function epilogue
   (unreachable for now; cross-function propagation is a later increment).

   This MUST run on EVERY try teardown, and a try is torn down at exactly one
   choke point: handle_next_reachable_block's generic pop of the first reachable
   block. A normal try reaches it because aot_compile_op_end marks the try
   reachable and delegates the pop here; a try exited by a `br` targeting the
   try's OWN end reaches it because op_br marked the try reachable -- and in that
   case op_end never runs, so finalizing only in op_end would leave catch_next
   without a terminator. Idempotent: a catch_next already terminated (finalized
   earlier, or cleared to NULL by catch_all which has no mismatch edge) is left
   untouched, so it is safe to call unconditionally on any popped block. */
static bool
aot_finalize_try_catch_next(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                            AOTBlock *block)
{
    LLVMBasicBlockRef save;
    AOTBlock *outer;
    bool ok;

    (void)func_ctx;
    if (block->label_type != LABEL_TYPE_TRY || !block->llvm_catch_next_block
        || LLVMGetBasicBlockTerminator(block->llvm_catch_next_block))
        return true;

    save = LLVMGetInsertBlock(comp_ctx->builder);
    outer = block->prev;
    while (outer && outer->label_type != LABEL_TYPE_TRY)
        outer = outer->prev;
    SET_BUILDER_POS(block->llvm_catch_next_block);
    ok = outer ? (LLVMBuildBr(comp_ctx->builder,
                              outer->llvm_catch_dispatch_block)
                  != NULL)
               : (LLVMBuildUnreachable(comp_ctx->builder) != NULL);
    if (!ok) {
        aot_set_last_error("llvm build terminator failed.");
        return false;
    }
    if (save)
        SET_BUILDER_POS(save);
    return true;
}

/* Compute a try's REAL end address. wasm_loader_find_block_addr returns the
   address of a try's FIRST catch for LABEL_TYPE_TRY (see wasm_loader.c: it stops
   and returns p-1 at the first depth-1 CATCH/CATCH_ALL/DELEGATE). Walk from that
   first catch across the remaining catch clauses to the structural end: skip
   each CATCH's tag-index LEB (CATCH_ALL has no immediate), then scan that
   handler body with find_block_addr to the next depth-1 catch/end, until the
   returned opcode is WASM_OP_END or WASM_OP_DELEGATE. */
static bool
aot_compute_try_real_end(uint8 *first_catch, uint8 *code_end,
                         uint8 **p_real_end)
{
    BlockAddr blk_cache[BLOCK_ADDR_CACHE_SIZE][BLOCK_ADDR_CONFLICT_SIZE];
    uint8 *addr = first_catch;
    uint8 *scan_start, *else_a, *next;
    uint64 tag_index;

    while (addr < code_end) {
        uint8 op = *addr;
        if (op == WASM_OP_END || op == WASM_OP_DELEGATE) {
            *p_real_end = addr;
            return true;
        }
        if (op != WASM_OP_CATCH && op != WASM_OP_CATCH_ALL) {
            aot_set_last_error("unexpected opcode scanning try catch clauses.");
            return false;
        }
        scan_start = addr + 1; /* skip the catch/catch_all opcode byte */
        if (op == WASM_OP_CATCH
            && !read_leb(&scan_start, code_end, 32, false, &tag_index, NULL, 0)) {
            aot_set_last_error("read catch tag index failed.");
            return false;
        }
        memset(blk_cache, 0, sizeof(blk_cache));
        else_a = NULL;
        next = NULL;
        if (!wasm_loader_find_block_addr(NULL, (BlockAddr *)blk_cache,
                                         scan_start, code_end,
                                         (uint8)LABEL_TYPE_TRY, &else_a,
                                         &next)) {
            aot_set_last_error("find try catch/end addr failed.");
            return false;
        }
        addr = next;
    }
    aot_set_last_error("try real end not found.");
    return false;
}
#endif

static bool
handle_next_reachable_block(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                            uint8 **p_frame_ip)
{
    AOTBlock *block = func_ctx->block_stack.block_list_end;
    AOTBlock *block_prev;
    AOTCompFrame *aot_frame = comp_ctx->aot_frame;
    uint8 *frame_ip = NULL;
    uint32 i;
    AOTFuncType *func_type;
    LLVMValueRef ret;
#if WASM_ENABLE_DEBUG_AOT != 0
    LLVMMetadataRef return_location;
#endif

    aot_checked_addr_list_destroy(func_ctx);
    bh_assert(block);

#if WASM_ENABLE_DEBUG_AOT != 0
    return_location = dwarf_gen_location(
        comp_ctx, func_ctx,
        (*p_frame_ip - 1) - comp_ctx->comp_data->wasm_module->buf_code);
#endif

    if (aot_frame) {
        /* Clear frame local variables since they have been committed */
        clear_frame_locals(aot_frame);
    }

    if (block->label_type == LABEL_TYPE_IF && block->llvm_else_block
        && *p_frame_ip <= block->wasm_code_else) {
        /* Clear value stack and start to translate else branch */
        aot_value_stack_destroy(comp_ctx, &block->value_stack);

        if (aot_frame) {
            /* Restore the frame sp */
            restore_frame_sp_for_op_else(block, aot_frame);
        }

        /* Recover parameters of else branch */
        for (i = 0; i < block->param_count; i++)
            PUSH(block->else_param_phis[i], block->param_types[i]);
        SET_BUILDER_POS(block->llvm_else_block);
        *p_frame_ip = block->wasm_code_else + 1;
        return true;
    }

    while (block && !block->is_reachable) {
#if WASM_ENABLE_EXCE_HANDLING != 0
        if (block->label_type == LABEL_TYPE_TRY) {
            /* Unwinding dead code inside a try -- after a throw in the body, or
               a catch handler that ended in a br/return/throw. The try's catch
               clauses live inline in the byte stream and must still be compiled,
               so do NOT pop the try here: scan to the next catch/catch_all/
               delegate/end at this try's depth and resume parsing there. The
               current (dead) block stays terminated; aot_compile_op_catch and
               aot_compile_op_end skip their fall-through when the builder sits on
               an already-terminated block. The try is torn down and finalized by
               its own op_end. Use the local frame_ip (advanced past any inner
               blocks already popped this unwind) as the scan origin. */
            BlockAddr blk_cache[BLOCK_ADDR_CACHE_SIZE][BLOCK_ADDR_CONFLICT_SIZE];
            uint8 *scan_start = frame_ip ? frame_ip + 1 : *p_frame_ip;
            uint8 *code_end =
                func_ctx->aot_func->code + func_ctx->aot_func->code_size;
            uint8 *else_a = NULL, *catch_or_end = NULL;
            memset(blk_cache, 0, sizeof(blk_cache));
            if (!wasm_loader_find_block_addr(NULL, (BlockAddr *)blk_cache,
                                             scan_start, code_end,
                                             (uint8)LABEL_TYPE_TRY, &else_a,
                                             &catch_or_end)) {
                aot_set_last_error("find try catch/end addr failed.");
                return false;
            }
            aot_value_stack_destroy(comp_ctx, &block->value_stack);
            *p_frame_ip = catch_or_end;
            return true;
        }
#endif
        block_prev = block->prev;
        block = aot_block_stack_pop(&func_ctx->block_stack);

        if (block->label_type == LABEL_TYPE_IF) {
            if (block->llvm_else_block && !block->skip_wasm_code_else
                && *p_frame_ip <= block->wasm_code_else) {
                /* Clear value stack and start to translate else branch */
                aot_value_stack_destroy(comp_ctx, &block->value_stack);

                if (aot_frame) {
                    /* Restore the frame sp */
                    restore_frame_sp_for_op_else(block, aot_frame);
                }

                SET_BUILDER_POS(block->llvm_else_block);
                *p_frame_ip = block->wasm_code_else + 1;
                /* Push back the block */
                aot_block_stack_push(&func_ctx->block_stack, block);
                /* Recover parameters of else branch */
                for (i = 0; i < block->param_count; i++)
                    PUSH(block->else_param_phis[i], block->param_types[i]);
                return true;
            }
            else if (block->llvm_end_block) {
                /* Remove unreachable basic block */
                LLVMDeleteBasicBlock(block->llvm_end_block);
                block->llvm_end_block = NULL;
            }
        }

        frame_ip = block->wasm_code_end;
        aot_block_destroy(comp_ctx, block);
        block = block_prev;
    }

    if (!block) {
        *p_frame_ip = frame_ip + 1;
        return true;
    }

    if (block->label_type == LABEL_TYPE_IF && block->llvm_else_block
        && !block->skip_wasm_code_else
        && *p_frame_ip <= block->wasm_code_else) {
        /* Clear value stack and start to translate else branch */
        aot_value_stack_destroy(comp_ctx, &block->value_stack);

        if (aot_frame) {
            /* Restore the frame sp */
            restore_frame_sp_for_op_else(block, aot_frame);
        }

        /* Recover parameters of else branch */
        for (i = 0; i < block->param_count; i++)
            PUSH(block->else_param_phis[i], block->param_types[i]);
        SET_BUILDER_POS(block->llvm_else_block);
        *p_frame_ip = block->wasm_code_else + 1;
        return true;
    }

#if WASM_ENABLE_EXCE_HANDLING != 0
    if (block->label_type == LABEL_TYPE_TRY
        && *p_frame_ip <= block->try_real_end) {
        /* A reachable try whose resume position is still at/inside the try is a
           mid-unwind teardown, NOT a completion: e.g. a `br` targeting the try's
           OWN end (op_br marked it reachable + branched to llvm_end_block, but
           bypassed op_end). The try's catch clauses live inline in the byte
           stream and still must be compiled, so do NOT pop the try here -- scan
           to the next catch/catch_all/delegate/end at this try's depth and
           resume parsing there. The try is torn down and finalized by its own
           op_end (which then takes the completion path below). This mirrors the
           dead-code unwinder's LABEL_TYPE_TRY case above. */
        BlockAddr blk_cache[BLOCK_ADDR_CACHE_SIZE][BLOCK_ADDR_CONFLICT_SIZE];
        uint8 *scan_start = frame_ip ? frame_ip + 1 : *p_frame_ip;
        uint8 *code_end =
            func_ctx->aot_func->code + func_ctx->aot_func->code_size;
        uint8 *else_a = NULL, *catch_or_end = NULL;
        memset(blk_cache, 0, sizeof(blk_cache));
        if (!wasm_loader_find_block_addr(NULL, (BlockAddr *)blk_cache,
                                         scan_start, code_end,
                                         (uint8)LABEL_TYPE_TRY, &else_a,
                                         &catch_or_end)) {
            aot_set_last_error("find try catch/end addr failed.");
            return false;
        }
        aot_value_stack_destroy(comp_ctx, &block->value_stack);
        *p_frame_ip = catch_or_end;
        return true;
    }

    /* Single choke point for try completion teardown: finalize the try's
       catch_next before it is popped. A completing try reaches here from its own
       op_end (the mid-unwind cases -- a throw, a handler ending in br/return/
       throw, or a br to the try's own end -- are handled above and defer teardown
       to that op_end). No-op for non-try blocks. Idempotent regardless. */
    if (!aot_finalize_try_catch_next(comp_ctx, func_ctx, block))
        goto fail;

    /* For a completing try, *p_frame_ip already points just past the real end
       (op_end advanced it). Do NOT overwrite it with wasm_code_end + 1: a try's
       wasm_code_end is its FIRST catch address, so that would rewind the parser
       into the catch's operand bytes and drop all code after the try (the
       miscompile this fixes). Every other block type has wasm_code_end == real
       end, so the original assignment is preserved for them. */
    if (block->label_type != LABEL_TYPE_TRY)
        *p_frame_ip = block->wasm_code_end + 1;
#else
    *p_frame_ip = block->wasm_code_end + 1;
#endif
    SET_BUILDER_POS(block->llvm_end_block);

    /* Pop block, push its return value, and destroy the block */
    block = aot_block_stack_pop(&func_ctx->block_stack);

    if (aot_frame) {
        /* Restore the frame sp */
        restore_frame_sp_for_op_end(block, aot_frame);
    }

    func_type = func_ctx->aot_func->func_type;
    for (i = 0; i < block->result_count; i++) {
        bh_assert(block->result_phis[i]);
        if (block->label_type != LABEL_TYPE_FUNCTION) {
            PUSH(block->result_phis[i], block->result_types[i]);
        }
        else {
            /* Store extra return values to function parameters */
            if (i != 0) {
                LLVMValueRef res;
                uint32 param_index = func_type->param_count + i;
                if (!(res = LLVMBuildStore(
                          comp_ctx->builder, block->result_phis[i],
                          LLVMGetParam(func_ctx->func, param_index)))) {
                    aot_set_last_error("llvm build store failed.");
                    goto fail;
                }
                LLVMSetAlignment(res, 1);
            }
        }
    }
    if (block->label_type == LABEL_TYPE_FUNCTION) {
        if (block->result_count) {
            /* Return the first return value */
            if (!(ret =
                      LLVMBuildRet(comp_ctx->builder, block->result_phis[0]))) {
                aot_set_last_error("llvm build return failed.");
                goto fail;
            }
#if WASM_ENABLE_DEBUG_AOT != 0
            if (return_location != NULL) {
                LLVMInstructionSetDebugLoc(ret, return_location);
            }
#endif
        }
        else {
            if (!(ret = LLVMBuildRetVoid(comp_ctx->builder))) {
                aot_set_last_error("llvm build return void failed.");
                goto fail;
            }
#if WASM_ENABLE_DEBUG_AOT != 0
            if (return_location != NULL) {
                LLVMInstructionSetDebugLoc(ret, return_location);
            }
#endif
        }
    }
    aot_block_destroy(comp_ctx, block);
    return true;
fail:
    return false;
}

static bool
push_aot_block_to_stack_and_pass_params(AOTCompContext *comp_ctx,
                                        AOTFuncContext *func_ctx,
                                        AOTBlock *block)
{
    uint32 i, param_index;
    LLVMValueRef value, br_inst;
    uint64 size;
    char name[32];
    LLVMBasicBlockRef block_curr = CURR_BLOCK();

    if (block->param_count) {
        size = sizeof(LLVMValueRef) * (uint64)block->param_count;
        if (size >= UINT32_MAX
            || !(block->param_phis = wasm_runtime_malloc((uint32)size))) {
            aot_set_last_error("allocate memory failed.");
            return false;
        }

        if (block->label_type == LABEL_TYPE_IF && !block->skip_wasm_code_else
            && !(block->else_param_phis = wasm_runtime_malloc((uint32)size))) {
            wasm_runtime_free(block->param_phis);
            block->param_phis = NULL;
            aot_set_last_error("allocate memory failed.");
            return false;
        }

        /* Create param phis */
        for (i = 0; i < block->param_count; i++) {
            if (block->llvm_entry_block) {
                SET_BUILDER_POS(block->llvm_entry_block);
                snprintf(name, sizeof(name), "%s%d_phi%d",
                         block_name_prefix[block->label_type],
                         block->block_index, i);
                if (!(block->param_phis[i] = LLVMBuildPhi(
                          comp_ctx->builder,
                          TO_LLVM_TYPE(block->param_types[i]), name))) {
                    aot_set_last_error("llvm build phi failed.");
                    goto fail;
                }
            }

            if (block->label_type == LABEL_TYPE_IF
                && !block->skip_wasm_code_else && block->llvm_else_block) {
                /* Build else param phis */
                SET_BUILDER_POS(block->llvm_else_block);
                snprintf(name, sizeof(name), "else%d_phi%d", block->block_index,
                         i);
                if (!(block->else_param_phis[i] = LLVMBuildPhi(
                          comp_ctx->builder,
                          TO_LLVM_TYPE(block->param_types[i]), name))) {
                    aot_set_last_error("llvm build phi failed.");
                    goto fail;
                }
            }
        }

        /* At this point, the branch instruction was already built to jump to
         * the new BB, to avoid generating zext instruction from the popped
         * operand that would come after branch instruction, we should position
         * the builder before the last branch instruction */
        br_inst = LLVMGetLastInstruction(block_curr);
        bh_assert(LLVMGetInstructionOpcode(br_inst) == LLVMBr);
        LLVMPositionBuilderBefore(comp_ctx->builder, br_inst);

        /* Pop param values from current block's
         * value stack and add to param phis.
         */
        for (i = 0; i < block->param_count; i++) {
            param_index = block->param_count - 1 - i;
            POP(value, block->param_types[param_index]);
            if (block->llvm_entry_block)
                /* Only add incoming phis if the entry block was created */
                ADD_TO_PARAM_PHIS(block, value, param_index);
            if (block->label_type == LABEL_TYPE_IF
                && !block->skip_wasm_code_else) {
                if (block->llvm_else_block) {
                    /* has else branch, add to else param phis */
                    LLVMAddIncoming(block->else_param_phis[param_index], &value,
                                    &block_curr, 1);
                }
                else {
                    /* no else branch, add to result phis */
                    CREATE_RESULT_VALUE_PHIS(block);
                    ADD_TO_RESULT_PHIS(block, value, param_index);
                }
            }
        }
    }

    /* Push the new block to block stack */
    aot_block_stack_push(&func_ctx->block_stack, block);
    if (comp_ctx->aot_frame) {
        block->frame_sp_begin = block->frame_sp_max_reached =
            comp_ctx->aot_frame->sp;
    }

    /* Push param phis to the new block */
    for (i = 0; i < block->param_count; i++) {
        if (block->llvm_entry_block)
            /* Push param phis if the entry basic block was created */
            PUSH(block->param_phis[i], block->param_types[i]);
        else {
            bh_assert(block->label_type == LABEL_TYPE_IF
                      && block->llvm_else_block && block->else_param_phis
                      && !block->skip_wasm_code_else);
            /* Push else param phis if we start to translate the
               else branch */
            PUSH(block->else_param_phis[i], block->param_types[i]);
        }
    }

    return true;

fail:
    if (block->param_phis) {
        wasm_runtime_free(block->param_phis);
        block->param_phis = NULL;
    }
    if (block->else_param_phis) {
        wasm_runtime_free(block->else_param_phis);
        block->else_param_phis = NULL;
    }
    return false;
}

bool
aot_compile_op_block(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                     uint8 **p_frame_ip, uint8 *frame_ip_end, uint32 label_type,
                     uint32 param_count, uint8 *param_types,
                     uint32 result_count, uint8 *result_types)
{
    BlockAddr block_addr_cache[BLOCK_ADDR_CACHE_SIZE][BLOCK_ADDR_CONFLICT_SIZE];
    AOTBlock *block;
    uint8 *else_addr, *end_addr;
    LLVMValueRef value;
    char name[32];

    /* Check block stack */
    if (!func_ctx->block_stack.block_list_end) {
        aot_set_last_error("WASM block stack underflow.");
        return false;
    }

    memset(block_addr_cache, 0, sizeof(block_addr_cache));

    /* Get block info */
    if (!(wasm_loader_find_block_addr(
            NULL, (BlockAddr *)block_addr_cache, *p_frame_ip, frame_ip_end,
            (uint8)label_type, &else_addr, &end_addr))) {
        aot_set_last_error("find block end addr failed.");
        return false;
    }

    /* Allocate memory */
    if (!(block = wasm_runtime_malloc(sizeof(AOTBlock)))) {
        aot_set_last_error("allocate memory failed.");
        return false;
    }
    memset(block, 0, sizeof(AOTBlock));
    if (param_count
        && !(block->param_types = wasm_runtime_malloc(param_count))) {
        aot_set_last_error("allocate memory failed.");
        goto fail;
    }
    if (result_count) {
        if (!(block->result_types = wasm_runtime_malloc(result_count))) {
            aot_set_last_error("allocate memory failed.");
            goto fail;
        }
    }

    /* Init aot block data */
    block->label_type = label_type;
    block->param_count = param_count;
    if (param_count) {
        bh_memcpy_s(block->param_types, param_count, param_types, param_count);
    }
    block->result_count = result_count;
    if (result_count) {
        bh_memcpy_s(block->result_types, result_count, result_types,
                    result_count);
    }
    block->wasm_code_else = else_addr;
    block->wasm_code_end = end_addr;
#if WASM_ENABLE_EXCE_HANDLING != 0
    /* For a try, end_addr is the FIRST catch, not the structural end. Record the
       real end so handle_next_reachable_block can tell a completed try (op_end)
       from a mid-unwind teardown (e.g. br to the try's own end). */
    if (label_type == LABEL_TYPE_TRY
        && !aot_compute_try_real_end(end_addr, frame_ip_end,
                                     &block->try_real_end))
        goto fail;
#endif
    block->block_index = func_ctx->block_stack.block_index[label_type];
    func_ctx->block_stack.block_index[label_type]++;

    if (comp_ctx->aot_frame) {
        if (label_type != LABEL_TYPE_BLOCK && comp_ctx->enable_gc
            && !aot_gen_commit_values(comp_ctx->aot_frame)) {
            goto fail;
        }
    }

    if (label_type == LABEL_TYPE_BLOCK || label_type == LABEL_TYPE_LOOP
#if WASM_ENABLE_EXCE_HANDLING != 0
        || label_type == LABEL_TYPE_TRY
#endif
    ) {
        /* Create block */
        format_block_name(name, sizeof(name), block->block_index, label_type,
                          LABEL_BEGIN);
        CREATE_BLOCK(block->llvm_entry_block, name);
        MOVE_BLOCK_AFTER_CURR(block->llvm_entry_block);
#if WASM_ENABLE_EXCE_HANDLING != 0
        if (label_type == LABEL_TYPE_TRY) {
            /* A `throw` (or a pending exception surfacing after a call) inside
               this try branches here; catch/catch_all populate it with the tag
               tests + handler bodies while walking the stream. Created up front
               so throw sites can target it before the catches are emitted. */
            CREATE_BLOCK(block->llvm_catch_dispatch_block, "try_catch_dispatch");
            block->llvm_catch_next_block = block->llvm_catch_dispatch_block;
            block->cur_catch_tag_index = -1;
        }
#endif
        /* Jump to the entry block */
        BUILD_BR(block->llvm_entry_block);
        if (!push_aot_block_to_stack_and_pass_params(comp_ctx, func_ctx, block))
            goto fail;
        /* Start to translate the block */
        SET_BUILDER_POS(block->llvm_entry_block);
        if (label_type == LABEL_TYPE_LOOP)
            aot_checked_addr_list_destroy(func_ctx);
    }
    else if (label_type == LABEL_TYPE_IF) {
        POP_COND(value);

        if (LLVMIsUndef(value)
#if LLVM_VERSION_NUMBER >= 12
            || LLVMIsPoison(value)
#endif
        ) {
            if (!(aot_emit_exception(comp_ctx, func_ctx, EXCE_INTEGER_OVERFLOW,
                                     false, NULL, NULL))) {
                goto fail;
            }
            aot_block_destroy(comp_ctx, block);
            return aot_handle_next_reachable_block(comp_ctx, func_ctx,
                                                   p_frame_ip);
        }

        if (!LLVMIsEfficientConstInt(value)) {
            /* Compare value is not constant, create condition br IR */
            /* Create entry block */
            format_block_name(name, sizeof(name), block->block_index,
                              label_type, LABEL_BEGIN);
            CREATE_BLOCK(block->llvm_entry_block, name);
            MOVE_BLOCK_AFTER_CURR(block->llvm_entry_block);

            /* Create end block */
            format_block_name(name, sizeof(name), block->block_index,
                              label_type, LABEL_END);
            CREATE_BLOCK(block->llvm_end_block, name);
            MOVE_BLOCK_AFTER(block->llvm_end_block, block->llvm_entry_block);

            if (else_addr) {
                /* Create else block */
                format_block_name(name, sizeof(name), block->block_index,
                                  label_type, LABEL_ELSE);
                CREATE_BLOCK(block->llvm_else_block, name);
                MOVE_BLOCK_AFTER(block->llvm_else_block,
                                 block->llvm_entry_block);
                /* Create condition br IR */
#if WASM_ENABLE_BRANCH_HINTS != 0
                LLVMValueRef br_if_val = NULL;
                BUILD_COND_BR_V(value, block->llvm_entry_block,
                                block->llvm_else_block, br_if_val);
                const uint32 off =
                    *p_frame_ip - func_ctx->aot_func->code_body_begin;
                aot_emit_branch_hint(comp_ctx, func_ctx, off, br_if_val);
#else
                BUILD_COND_BR(value, block->llvm_entry_block,
                              block->llvm_else_block);
#endif
            }
            else {
                /* Create condition br IR */
#if WASM_ENABLE_BRANCH_HINTS != 0
                LLVMValueRef br_if_val = NULL;
                BUILD_COND_BR_V(value, block->llvm_entry_block,
                                block->llvm_end_block, br_if_val);
                const uint32 off =
                    *p_frame_ip - func_ctx->aot_func->code_body_begin;
                aot_emit_branch_hint(comp_ctx, func_ctx, off, br_if_val);
#else
                BUILD_COND_BR(value, block->llvm_entry_block,
                              block->llvm_end_block);
#endif
                block->is_reachable = true;
            }
            if (!push_aot_block_to_stack_and_pass_params(comp_ctx, func_ctx,
                                                         block))
                goto fail;
            /* Start to translate if branch of BLOCK if */
            SET_BUILDER_POS(block->llvm_entry_block);
        }
        else {
            if ((int32)LLVMConstIntGetZExtValue(value) != 0) {
                /* Compare value is not 0, condition is true, else branch of
                   BLOCK if cannot be reached */
                block->skip_wasm_code_else = true;
                /* Create entry block */
                format_block_name(name, sizeof(name), block->block_index,
                                  label_type, LABEL_BEGIN);
                CREATE_BLOCK(block->llvm_entry_block, name);
                MOVE_BLOCK_AFTER_CURR(block->llvm_entry_block);
                /* Jump to the entry block */
                BUILD_BR(block->llvm_entry_block);
                if (!push_aot_block_to_stack_and_pass_params(comp_ctx, func_ctx,
                                                             block))
                    goto fail;
                /* Start to translate the if branch */
                SET_BUILDER_POS(block->llvm_entry_block);
            }
            else {
                /* Compare value is not 0, condition is false, if branch of
                   BLOCK if cannot be reached */
                if (else_addr) {
                    /* Create else block */
                    format_block_name(name, sizeof(name), block->block_index,
                                      label_type, LABEL_ELSE);
                    CREATE_BLOCK(block->llvm_else_block, name);
                    MOVE_BLOCK_AFTER_CURR(block->llvm_else_block);
                    /* Jump to the else block */
                    BUILD_BR(block->llvm_else_block);
                    if (!push_aot_block_to_stack_and_pass_params(
                            comp_ctx, func_ctx, block))
                        goto fail;
                    /* Start to translate the else branch */
                    SET_BUILDER_POS(block->llvm_else_block);
                    *p_frame_ip = else_addr + 1;
                }
                else {
                    /* skip the block */
                    aot_block_destroy(comp_ctx, block);
                    *p_frame_ip = end_addr + 1;
                }
            }
        }
    }
    else {
        aot_set_last_error("Invalid block type.");
        goto fail;
    }

    return true;
fail:
    aot_block_destroy(comp_ctx, block);
    return false;
}

bool
aot_compile_op_else(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                    uint8 **p_frame_ip)
{
    AOTBlock *block = func_ctx->block_stack.block_list_end;
    LLVMValueRef value;
    AOTCompFrame *aot_frame = comp_ctx->aot_frame;
    char name[32];
    uint32 i, result_index;

    /* Check block */
    if (!block) {
        aot_set_last_error("WASM block stack underflow.");
        return false;
    }
    if (block->label_type != LABEL_TYPE_IF
        || (!block->skip_wasm_code_else && !block->llvm_else_block)) {
        aot_set_last_error("Invalid WASM block type.");
        return false;
    }

    /* Create end block if needed */
    if (!block->llvm_end_block) {
        format_block_name(name, sizeof(name), block->block_index,
                          block->label_type, LABEL_END);
        CREATE_BLOCK(block->llvm_end_block, name);
        if (block->llvm_else_block)
            MOVE_BLOCK_AFTER(block->llvm_end_block, block->llvm_else_block);
        else
            MOVE_BLOCK_AFTER_CURR(block->llvm_end_block);
    }

    block->is_reachable = true;

    /* Comes from the if branch of BLOCK if */
    CREATE_RESULT_VALUE_PHIS(block);
    for (i = 0; i < block->result_count; i++) {
        result_index = block->result_count - 1 - i;
        POP(value, block->result_types[result_index]);
        ADD_TO_RESULT_PHIS(block, value, result_index);
    }

    if (aot_frame) {
        bh_assert(block->frame_sp_begin == aot_frame->sp);
        if (comp_ctx->enable_gc && !aot_gen_commit_values(aot_frame)) {
            goto fail;
        }
    }

    /* Jump to end block */
    BUILD_BR(block->llvm_end_block);

    if (!block->skip_wasm_code_else && block->llvm_else_block) {
        /* Clear value stack, recover param values
           and start to translate else branch. */
        aot_value_stack_destroy(comp_ctx, &block->value_stack);

        if (comp_ctx->aot_frame) {
            clear_frame_locals(aot_frame);
            restore_frame_sp_for_op_else(block, aot_frame);
        }

        for (i = 0; i < block->param_count; i++)
            PUSH(block->else_param_phis[i], block->param_types[i]);
        SET_BUILDER_POS(block->llvm_else_block);
        aot_checked_addr_list_destroy(func_ctx);
        return true;
    }

    /* No else branch or no need to translate else branch */
    block->is_reachable = true;
    return handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
fail:
    return false;
}

bool
aot_compile_op_end(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                   uint8 **p_frame_ip)
{
    AOTBlock *block;
    LLVMValueRef value;
    LLVMBasicBlockRef next_llvm_end_block;
    char name[32];
    uint32 i, result_index;

    /* Check block stack */
    if (!(block = func_ctx->block_stack.block_list_end)) {
        aot_set_last_error("WASM block stack underflow.");
        return false;
    }

#if WASM_ENABLE_EXCE_HANDLING != 0
    /* A try's catch_next (last-catch mismatch edge) is finalized on teardown at
       the single choke point in handle_next_reachable_block, reached below once
       the try is marked reachable -- see aot_finalize_try_catch_next. */
#endif

    /* Create the end block */
    if (!block->llvm_end_block) {
        format_block_name(name, sizeof(name), block->block_index,
                          block->label_type, LABEL_END);
        CREATE_BLOCK(block->llvm_end_block, name);
        if ((next_llvm_end_block = find_next_llvm_end_block(block)))
            MOVE_BLOCK_BEFORE(block->llvm_end_block, next_llvm_end_block);
    }

    /* For a try, the byte stream reaches this END with the builder sitting on an
       already-terminated block when the try body / last catch handler ended in a
       throw/rethrow/br/return rather than falling through (the unwinder resumes
       parsing at the catches/end without repositioning the builder). Nothing more
       may be emitted into that dead block -- not the frame commit, the result
       pop, nor a fall-through branch. The try's live result already reached
       llvm_end_block via aot_compile_op_catch. */
    bool cur_live = true;
#if WASM_ENABLE_EXCE_HANDLING != 0
    if (block->label_type == LABEL_TYPE_TRY) {
        LLVMBasicBlockRef cur_bb = LLVMGetInsertBlock(comp_ctx->builder);
        cur_live = !(cur_bb && LLVMGetBasicBlockTerminator(cur_bb));
    }
#endif

    if (comp_ctx->aot_frame && cur_live) {
        if (block->label_type != LABEL_TYPE_FUNCTION && comp_ctx->enable_gc
            && !aot_gen_commit_values(comp_ctx->aot_frame)) {
            return false;
        }
    }

    /* Handle block result values */
    CREATE_RESULT_VALUE_PHIS(block);
    if (cur_live) {
        for (i = 0; i < block->result_count; i++) {
            value = NULL;
            result_index = block->result_count - 1 - i;
            POP(value, block->result_types[result_index]);
            bh_assert(value);
            ADD_TO_RESULT_PHIS(block, value, result_index);
        }

        if (comp_ctx->aot_frame) {
            bh_assert(comp_ctx->aot_frame->sp == block->frame_sp_begin);
        }

        /* Jump to the end block */
        BUILD_BR(block->llvm_end_block);
    }

    block->is_reachable = true;
    return handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
fail:
    return false;
}

bool
check_suspend_flags(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                    bool check_terminate_and_suspend)
{
    LLVMValueRef terminate_addr, terminate_flags, flag, offset, res;
    LLVMBasicBlockRef terminate_block, non_terminate_block;
    AOTFuncType *aot_func_type = func_ctx->aot_func->func_type;
    bool is_shared_memory =
        comp_ctx->comp_data->memories[0].flags & 0x02 ? true : false;

    /* Only need to check the suspend flags when memory is shared since
       shared memory must be enabled for multi-threading */
    if (!is_shared_memory) {
        return true;
    }

    /* Offset of suspend_flags */
    offset = I32_FIVE;

    if (!(terminate_addr = LLVMBuildInBoundsGEP2(
              comp_ctx->builder, OPQ_PTR_TYPE, func_ctx->exec_env, &offset, 1,
              "terminate_addr"))) {
        aot_set_last_error("llvm build in bounds gep failed");
        return false;
    }
    if (!(terminate_addr =
              LLVMBuildBitCast(comp_ctx->builder, terminate_addr,
                               INT32_PTR_TYPE, "terminate_addr_ptr"))) {
        aot_set_last_error("llvm build bit cast failed");
        return false;
    }

    if (!(terminate_flags =
              LLVMBuildLoad2(comp_ctx->builder, I32_TYPE, terminate_addr,
                             "terminate_flags"))) {
        aot_set_last_error("llvm build LOAD failed");
        return false;
    }
    /* Set terminate_flags memory access to volatile, so that the value
        will always be loaded from memory rather than register */
    LLVMSetVolatile(terminate_flags, true);

    if (!(flag = LLVMBuildAnd(comp_ctx->builder, terminate_flags, I32_ONE,
                              "termination_flag"))) {
        aot_set_last_error("llvm build AND failed");
        return false;
    }

    CREATE_BLOCK(non_terminate_block, "non_terminate");
    MOVE_BLOCK_AFTER_CURR(non_terminate_block);

    CREATE_BLOCK(terminate_block, "terminate");
    MOVE_BLOCK_AFTER_CURR(terminate_block);

    BUILD_ICMP(LLVMIntEQ, flag, I32_ZERO, res, "flag_terminate");
    BUILD_COND_BR(res, non_terminate_block, terminate_block);

    /* Move builder to terminate block */
    SET_BUILDER_POS(terminate_block);
    if (!aot_build_zero_function_ret(comp_ctx, func_ctx, aot_func_type)) {
        goto fail;
    }

    /* Move builder to non terminate block */
    SET_BUILDER_POS(non_terminate_block);
    return true;

fail:
    return false;
}

bool
aot_compile_op_br(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                  uint32 br_depth, uint8 **p_frame_ip)
{
    AOTBlock *block_dst;
    LLVMValueRef value_ret, value_param;
    LLVMBasicBlockRef next_llvm_end_block;
    char name[32];
    uint32 i, param_index, result_index;

    if (!(block_dst = get_target_block(func_ctx, br_depth))) {
        return false;
    }

    if (comp_ctx->aot_frame) {
        if (comp_ctx->enable_gc && !aot_gen_commit_values(comp_ctx->aot_frame))
            return false;

        if (block_dst->label_type == LABEL_TYPE_LOOP) {
            if (comp_ctx->enable_thread_mgr) {
                /* Commit sp when GC is enabled, don't commit ip */
                if (!aot_gen_commit_sp_ip(comp_ctx->aot_frame,
                                          comp_ctx->enable_gc, false))
                    return false;
            }
        }
        else {
            if (comp_ctx->aot_frame->sp > block_dst->frame_sp_max_reached)
                block_dst->frame_sp_max_reached = comp_ctx->aot_frame->sp;
        }
    }

    /* Terminate or suspend current thread only when this is a backward jump */
    if (comp_ctx->enable_thread_mgr
        && block_dst->label_type == LABEL_TYPE_LOOP) {
        if (!check_suspend_flags(comp_ctx, func_ctx, true))
            return false;
    }

    if (block_dst->label_type == LABEL_TYPE_LOOP) {
        /* Dest block is Loop block */
        /* Handle Loop parameters */
        for (i = 0; i < block_dst->param_count; i++) {
            param_index = block_dst->param_count - 1 - i;
            POP(value_param, block_dst->param_types[param_index]);
            ADD_TO_PARAM_PHIS(block_dst, value_param, param_index);
        }
        BUILD_BR(block_dst->llvm_entry_block);
    }
    else {
        /* Dest block is Block/If/Function block */
        /* Create the end block */
        if (!block_dst->llvm_end_block) {
            format_block_name(name, sizeof(name), block_dst->block_index,
                              block_dst->label_type, LABEL_END);
            CREATE_BLOCK(block_dst->llvm_end_block, name);
            if ((next_llvm_end_block = find_next_llvm_end_block(block_dst)))
                MOVE_BLOCK_BEFORE(block_dst->llvm_end_block,
                                  next_llvm_end_block);
        }

        block_dst->is_reachable = true;

        /* Handle result values */
        CREATE_RESULT_VALUE_PHIS(block_dst);
        for (i = 0; i < block_dst->result_count; i++) {
            result_index = block_dst->result_count - 1 - i;
            POP(value_ret, block_dst->result_types[result_index]);
            ADD_TO_RESULT_PHIS(block_dst, value_ret, result_index);
        }
        /* Jump to the end block */
        BUILD_BR(block_dst->llvm_end_block);
    }

    return handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
fail:
    return false;
}

static bool
aot_compile_conditional_br(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                           LLVMValueRef value_cmp, uint8 **p_frame_ip)
{
    AOTBlock *block_dst;
    LLVMValueRef value, *values = NULL;
    LLVMBasicBlockRef llvm_else_block, next_llvm_end_block;
    char name[32];
    uint32 i, param_index, result_index;
    uint64 size;

    // ip is advanced by one byte for the opcode
#if WASM_ENABLE_BRANCH_HINTS != 0
    uint32 instr_offset =
        (*p_frame_ip - 0x1) - (func_ctx->aot_func->code_body_begin);
#else
    uint32 instr_offset = 0;
#endif
    uint64 br_depth;
    if (!read_leb(p_frame_ip, *p_frame_ip + 5, 32, false, &br_depth, NULL, 0))
        return false;

    if (!(block_dst = get_target_block(func_ctx, br_depth))) {
        return false;
    }

    if (comp_ctx->aot_frame) {
        if (comp_ctx->enable_gc && !aot_gen_commit_values(comp_ctx->aot_frame))
            return false;

        if (block_dst->label_type == LABEL_TYPE_LOOP) {
            if (comp_ctx->enable_thread_mgr) {
                /* Commit sp when GC is enabled, don't commit ip */
                if (!aot_gen_commit_sp_ip(comp_ctx->aot_frame,
                                          comp_ctx->enable_gc, false))
                    return false;
            }
        }
        else {
            if (comp_ctx->aot_frame->sp > block_dst->frame_sp_max_reached)
                block_dst->frame_sp_max_reached = comp_ctx->aot_frame->sp;
        }
    }

    /* Terminate or suspend current thread only when this is
       a backward jump */
    if (comp_ctx->enable_thread_mgr
        && block_dst->label_type == LABEL_TYPE_LOOP) {
        if (!check_suspend_flags(comp_ctx, func_ctx, true))
            return false;
    }

    if (LLVMIsUndef(value_cmp)
#if LLVM_VERSION_NUMBER >= 12
        || LLVMIsPoison(value_cmp)
#endif
    ) {
        if (!(aot_emit_exception(comp_ctx, func_ctx, EXCE_INTEGER_OVERFLOW,
                                 false, NULL, NULL))) {
            goto fail;
        }
        return aot_handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
    }

    if (!LLVMIsEfficientConstInt(value_cmp)) {
        /* Compare value is not constant, create condition br IR */

        /* Create llvm else block */
        CREATE_BLOCK(llvm_else_block, "br_if_else");
        MOVE_BLOCK_AFTER_CURR(llvm_else_block);

        if (block_dst->label_type == LABEL_TYPE_LOOP) {
            /* Dest block is Loop block */
            /* Handle Loop parameters */
            if (block_dst->param_count) {
                size = sizeof(LLVMValueRef) * (uint64)block_dst->param_count;
                if (size >= UINT32_MAX
                    || !(values = wasm_runtime_malloc((uint32)size))) {
                    aot_set_last_error("allocate memory failed.");
                    goto fail;
                }
                for (i = 0; i < block_dst->param_count; i++) {
                    param_index = block_dst->param_count - 1 - i;
                    POP(value, block_dst->param_types[param_index]);
                    ADD_TO_PARAM_PHIS(block_dst, value, param_index);
                    values[param_index] = value;
                }
                for (i = 0; i < block_dst->param_count; i++) {
                    PUSH(values[i], block_dst->param_types[i]);
                }
                wasm_runtime_free(values);
                values = NULL;
            }

#if WASM_ENABLE_BRANCH_HINTS != 0
            LLVMValueRef br_if_val = NULL;
            BUILD_COND_BR_V(value_cmp, block_dst->llvm_entry_block,
                            llvm_else_block, br_if_val);
            aot_emit_branch_hint(comp_ctx, func_ctx, instr_offset, br_if_val);
#else
            BUILD_COND_BR(value_cmp, block_dst->llvm_entry_block,
                          llvm_else_block);
#endif

            /* Move builder to else block */
            SET_BUILDER_POS(llvm_else_block);
        }
        else {
            /* Dest block is Block/If/Function block */
            /* Create the end block */
            if (!block_dst->llvm_end_block) {
                format_block_name(name, sizeof(name), block_dst->block_index,
                                  block_dst->label_type, LABEL_END);
                CREATE_BLOCK(block_dst->llvm_end_block, name);
                if ((next_llvm_end_block = find_next_llvm_end_block(block_dst)))
                    MOVE_BLOCK_BEFORE(block_dst->llvm_end_block,
                                      next_llvm_end_block);
            }

            /* Set reachable flag and create condition br IR */
            block_dst->is_reachable = true;

            /* Handle result values */
            if (block_dst->result_count) {
                size = sizeof(LLVMValueRef) * (uint64)block_dst->result_count;
                if (size >= UINT32_MAX
                    || !(values = wasm_runtime_malloc((uint32)size))) {
                    aot_set_last_error("allocate memory failed.");
                    goto fail;
                }
                CREATE_RESULT_VALUE_PHIS(block_dst);
                for (i = 0; i < block_dst->result_count; i++) {
                    result_index = block_dst->result_count - 1 - i;
                    POP(value, block_dst->result_types[result_index]);
                    values[result_index] = value;
                    ADD_TO_RESULT_PHIS(block_dst, value, result_index);
                }
                for (i = 0; i < block_dst->result_count; i++) {
                    PUSH(values[i], block_dst->result_types[i]);
                }
                wasm_runtime_free(values);
                values = NULL;
            }

            /* Condition jump to end block */
#if WASM_ENABLE_BRANCH_HINTS != 0
            LLVMValueRef br_if_val = NULL;
            BUILD_COND_BR_V(value_cmp, block_dst->llvm_end_block,
                            llvm_else_block, br_if_val);
            aot_emit_branch_hint(comp_ctx, func_ctx, instr_offset, br_if_val);
#else
            BUILD_COND_BR(value_cmp, block_dst->llvm_end_block,
                          llvm_else_block);
#endif
            /* Move builder to else block */
            SET_BUILDER_POS(llvm_else_block);
        }
    }
    else {
        if ((int32)LLVMConstIntGetZExtValue(value_cmp) != 0) {
            /* Compare value is not 0, condition is true, same as op_br */
            return aot_compile_op_br(comp_ctx, func_ctx, br_depth, p_frame_ip);
        }
        else {
            /* Compare value is not 0, condition is false, skip br_if */
            return true;
        }
    }
    return true;
fail:
    if (values)
        wasm_runtime_free(values);
    return false;
}

bool
aot_compile_op_br_if(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                     uint8 **p_frame_ip)
{
    LLVMValueRef value_cmp;

    POP_COND(value_cmp);

    return aot_compile_conditional_br(comp_ctx, func_ctx, value_cmp,
                                      p_frame_ip);
fail:
    return false;
}

bool
aot_compile_op_br_table(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                        uint32 *br_depths, uint32 br_count, uint8 **p_frame_ip)
{
    uint32 i, j;
    LLVMValueRef value_switch, value_cmp, value_case, value, *values = NULL;
    LLVMBasicBlockRef default_llvm_block = NULL, target_llvm_block;
    LLVMBasicBlockRef next_llvm_end_block;
    AOTBlock *target_block;
    uint32 br_depth, depth_idx;
    uint32 param_index, result_index;
    uint64 size;
    char name[32];

    POP_I32(value_cmp);

    if (LLVMIsUndef(value_cmp)
#if LLVM_VERSION_NUMBER >= 12
        || LLVMIsPoison(value_cmp)
#endif
    ) {
        if (!(aot_emit_exception(comp_ctx, func_ctx, EXCE_INTEGER_OVERFLOW,
                                 false, NULL, NULL))) {
            goto fail;
        }
        return aot_handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
    }

    /*
     * if (value_cmp > br_count)
     *   value_cmp = br_count;
     */
    LLVMValueRef br_count_value = I32_CONST(br_count);
    CHECK_LLVM_CONST(br_count_value);

    LLVMValueRef clap_value_cmp_cond =
        LLVMBuildICmp(comp_ctx->builder, LLVMIntUGT, value_cmp, br_count_value,
                      "cmp_w_br_count");
    if (!clap_value_cmp_cond) {
        aot_set_last_error("llvm build icmp failed.");
        return false;
    }

    value_cmp = LLVMBuildSelect(comp_ctx->builder, clap_value_cmp_cond,
                                br_count_value, value_cmp, "clap_value_cmp");
    if (!value_cmp) {
        aot_set_last_error("llvm build select failed.");
        return false;
    }

    if (!LLVMIsEfficientConstInt(value_cmp)) {
        if (comp_ctx->aot_frame) {
            if (comp_ctx->enable_gc
                && !aot_gen_commit_values(comp_ctx->aot_frame))
                return false;

            if (comp_ctx->enable_thread_mgr) {
                /* Commit sp when GC is enabled, don't commit ip */
                if (!aot_gen_commit_sp_ip(comp_ctx->aot_frame,
                                          comp_ctx->enable_gc, false))
                    return false;
            }

            for (i = 0; i <= br_count; i++) {
                target_block = get_target_block(func_ctx, br_depths[i]);
                if (!target_block)
                    return false;
                if (target_block->label_type != LABEL_TYPE_LOOP) {
                    if (comp_ctx->aot_frame->sp
                        > target_block->frame_sp_max_reached)
                        target_block->frame_sp_max_reached =
                            comp_ctx->aot_frame->sp;
                }
            }
        }

        if (comp_ctx->enable_thread_mgr) {
            for (i = 0; i <= br_count; i++) {
                target_block = get_target_block(func_ctx, br_depths[i]);
                if (!target_block)
                    return false;
                /* Terminate or suspend current thread only when this is a
                   backward jump */
                if (target_block->label_type == LABEL_TYPE_LOOP) {
                    if (!check_suspend_flags(comp_ctx, func_ctx, true))
                        return false;
                    break;
                }
            }
        }

        /* Compare value is not constant, create switch IR */
        for (i = 0; i <= br_count; i++) {
            target_block = get_target_block(func_ctx, br_depths[i]);
            if (!target_block)
                return false;

            if (target_block->label_type != LABEL_TYPE_LOOP) {
                /* Dest block is Block/If/Function block */
                /* Create the end block */
                if (!target_block->llvm_end_block) {
                    format_block_name(name, sizeof(name),
                                      target_block->block_index,
                                      target_block->label_type, LABEL_END);
                    CREATE_BLOCK(target_block->llvm_end_block, name);
                    if ((next_llvm_end_block =
                             find_next_llvm_end_block(target_block)))
                        MOVE_BLOCK_BEFORE(target_block->llvm_end_block,
                                          next_llvm_end_block);
                }
                /* Handle result values */
                if (target_block->result_count) {
                    size = sizeof(LLVMValueRef)
                           * (uint64)target_block->result_count;
                    if (size >= UINT32_MAX
                        || !(values = wasm_runtime_malloc((uint32)size))) {
                        aot_set_last_error("allocate memory failed.");
                        goto fail;
                    }
                    CREATE_RESULT_VALUE_PHIS(target_block);
                    for (j = 0; j < target_block->result_count; j++) {
                        result_index = target_block->result_count - 1 - j;
                        POP(value, target_block->result_types[result_index]);
                        values[result_index] = value;
                        ADD_TO_RESULT_PHIS(target_block, value, result_index);
                    }
                    for (j = 0; j < target_block->result_count; j++) {
                        PUSH(values[j], target_block->result_types[j]);
                    }
                    wasm_runtime_free(values);
                    values = NULL;
                }
                target_block->is_reachable = true;
                if (i == br_count)
                    default_llvm_block = target_block->llvm_end_block;
            }
            else {
                /* Handle Loop parameters */
                if (target_block->param_count) {
                    size = sizeof(LLVMValueRef)
                           * (uint64)target_block->param_count;
                    if (size >= UINT32_MAX
                        || !(values = wasm_runtime_malloc((uint32)size))) {
                        aot_set_last_error("allocate memory failed.");
                        goto fail;
                    }
                    for (j = 0; j < target_block->param_count; j++) {
                        param_index = target_block->param_count - 1 - j;
                        POP(value, target_block->param_types[param_index]);
                        values[param_index] = value;
                        ADD_TO_PARAM_PHIS(target_block, value, param_index);
                    }
                    for (j = 0; j < target_block->param_count; j++) {
                        PUSH(values[j], target_block->param_types[j]);
                    }
                    wasm_runtime_free(values);
                    values = NULL;
                }
                if (i == br_count)
                    default_llvm_block = target_block->llvm_entry_block;
            }
        }

        /* Create switch IR */
        if (!(value_switch = LLVMBuildSwitch(comp_ctx->builder, value_cmp,
                                             default_llvm_block, br_count))) {
            aot_set_last_error("llvm build switch failed.");
            return false;
        }

        /* Add each case for switch IR */
        for (i = 0; i < br_count; i++) {
            value_case = I32_CONST(i);
            CHECK_LLVM_CONST(value_case);
            target_block = get_target_block(func_ctx, br_depths[i]);
            if (!target_block)
                return false;
            target_llvm_block = target_block->label_type != LABEL_TYPE_LOOP
                                    ? target_block->llvm_end_block
                                    : target_block->llvm_entry_block;
            LLVMAddCase(value_switch, value_case, target_llvm_block);
        }

        return handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
    }
    else {
        /* Compare value is constant, create br IR */
        depth_idx = (uint32)LLVMConstIntGetZExtValue(value_cmp);
        br_depth = br_depths[br_count];
        if (depth_idx < br_count) {
            br_depth = br_depths[depth_idx];
        }
        return aot_compile_op_br(comp_ctx, func_ctx, br_depth, p_frame_ip);
    }
fail:
    if (values)
        wasm_runtime_free(values);
    return false;
}

bool
aot_compile_op_return(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                      uint8 **p_frame_ip)
{
    AOTBlock *block_func = func_ctx->block_stack.block_list_head;
    LLVMValueRef value;
    LLVMValueRef ret;
    AOTFuncType *func_type;
    uint32 i, param_index, result_index;
#if WASM_ENABLE_DEBUG_AOT != 0
    LLVMMetadataRef return_location;
#endif

    bh_assert(block_func);
    func_type = func_ctx->aot_func->func_type;

#if WASM_ENABLE_DEBUG_AOT != 0
    return_location = dwarf_gen_location(
        comp_ctx, func_ctx,
        (*p_frame_ip - 1) - comp_ctx->comp_data->wasm_module->buf_code);
#endif

    if (comp_ctx->aux_stack_frame_type
        && comp_ctx->call_stack_features.frame_per_function
        && !aot_free_frame_per_function_frame_for_aot_func(comp_ctx,
                                                           func_ctx)) {
        return false;
    }

    if (block_func->result_count) {
        /* Store extra result values to function parameters */
        for (i = 0; i < block_func->result_count - 1; i++) {
            LLVMValueRef res;
            result_index = block_func->result_count - 1 - i;
            POP(value, block_func->result_types[result_index]);
            param_index = func_type->param_count + result_index;
            if (!(res = LLVMBuildStore(
                      comp_ctx->builder, value,
                      LLVMGetParam(func_ctx->func, param_index)))) {
                aot_set_last_error("llvm build store failed.");
                goto fail;
            }
            LLVMSetAlignment(res, 1);
        }
        /* Return the first result value */
        POP(value, block_func->result_types[0]);
        if (!(ret = LLVMBuildRet(comp_ctx->builder, value))) {
            aot_set_last_error("llvm build return failed.");
            goto fail;
        }
#if WASM_ENABLE_DEBUG_AOT != 0
        LLVMInstructionSetDebugLoc(ret, return_location);
#endif
    }
    else {
        if (!(ret = LLVMBuildRetVoid(comp_ctx->builder))) {
            aot_set_last_error("llvm build return void failed.");
            goto fail;
        }
#if WASM_ENABLE_DEBUG_AOT != 0
        LLVMInstructionSetDebugLoc(ret, return_location);
#endif
    }

    return handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
fail:
    return false;
}

bool
aot_compile_op_unreachable(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                           uint8 **p_frame_ip)
{
    if (!aot_emit_exception(comp_ctx, func_ctx, EXCE_UNREACHABLE, false, NULL,
                            NULL))
        return false;

    return handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
}

bool
aot_handle_next_reachable_block(AOTCompContext *comp_ctx,
                                AOTFuncContext *func_ctx, uint8 **p_frame_ip)
{
    return handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
}

#if WASM_ENABLE_GC != 0
static bool
commit_gc_and_check_suspend_flags(AOTCompContext *comp_ctx,
                                  AOTFuncContext *func_ctx, uint32 br_depth)
{
    AOTBlock *block_dst;

    if (!(block_dst = get_target_block(func_ctx, br_depth))) {
        return false;
    }

    if (comp_ctx->aot_frame) {
        /* Note that GC is enabled, no need to check it again */
        if (!aot_gen_commit_values(comp_ctx->aot_frame))
            return false;

        if (block_dst->label_type == LABEL_TYPE_LOOP) {
            if (comp_ctx->enable_thread_mgr) {
                /* Note that GC is enabled, no need to check it again */
                if (!aot_gen_commit_sp_ip(comp_ctx->aot_frame, true, false))
                    return false;
            }
        }
        else {
            if (comp_ctx->aot_frame->sp > block_dst->frame_sp_max_reached)
                block_dst->frame_sp_max_reached = comp_ctx->aot_frame->sp;
        }
    }

    /* Terminate or suspend current thread only when this is
       a backward jump */
    if (comp_ctx->enable_thread_mgr
        && block_dst->label_type == LABEL_TYPE_LOOP) {
        if (!check_suspend_flags(comp_ctx, func_ctx, true))
            return false;
    }

    return true;
}

static bool
compile_gc_cond_br(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                   uint32 br_depth, LLVMValueRef value_cmp)
{
    AOTBlock *block_dst;
    LLVMValueRef value, *values = NULL;
    LLVMBasicBlockRef llvm_else_block, next_llvm_end_block;
    char name[32];
    uint32 i, param_index, result_index;
    uint64 size;

    if (!(block_dst = get_target_block(func_ctx, br_depth))) {
        return false;
    }

    /* Create llvm else block */
    CREATE_BLOCK(llvm_else_block, "br_if_else");
    MOVE_BLOCK_AFTER_CURR(llvm_else_block);

    if (block_dst->label_type == LABEL_TYPE_LOOP) {
        /* Dest block is Loop block */
        /* Handle Loop parameters */
        if (block_dst->param_count) {
            size = sizeof(LLVMValueRef) * (uint64)block_dst->param_count;
            if (size >= UINT32_MAX
                || !(values = wasm_runtime_malloc((uint32)size))) {
                aot_set_last_error("allocate memory failed.");
                goto fail;
            }
            for (i = 0; i < block_dst->param_count; i++) {
                param_index = block_dst->param_count - 1 - i;
                POP(value, block_dst->param_types[param_index]);
                ADD_TO_PARAM_PHIS(block_dst, value, param_index);
                values[param_index] = value;
            }
            for (i = 0; i < block_dst->param_count; i++) {
                PUSH(values[i], block_dst->param_types[i]);
            }
            wasm_runtime_free(values);
            values = NULL;
        }

        BUILD_COND_BR(value_cmp, block_dst->llvm_entry_block, llvm_else_block);

        /* Move builder to else block */
        SET_BUILDER_POS(llvm_else_block);
    }
    else {
        /* Dest block is Block/If/Function block */
        /* Create the end block */
        if (!block_dst->llvm_end_block) {
            format_block_name(name, sizeof(name), block_dst->block_index,
                              block_dst->label_type, LABEL_END);
            CREATE_BLOCK(block_dst->llvm_end_block, name);
            if ((next_llvm_end_block = find_next_llvm_end_block(block_dst)))
                MOVE_BLOCK_BEFORE(block_dst->llvm_end_block,
                                  next_llvm_end_block);
        }

        /* Set reachable flag and create condition br IR */
        block_dst->is_reachable = true;

        /* Handle result values */
        if (block_dst->result_count) {
            size = sizeof(LLVMValueRef) * (uint64)block_dst->result_count;
            if (size >= UINT32_MAX
                || !(values = wasm_runtime_malloc((uint32)size))) {
                aot_set_last_error("allocate memory failed.");
                goto fail;
            }
            CREATE_RESULT_VALUE_PHIS(block_dst);
            for (i = 0; i < block_dst->result_count; i++) {
                result_index = block_dst->result_count - 1 - i;
                POP(value, block_dst->result_types[result_index]);
                values[result_index] = value;
                ADD_TO_RESULT_PHIS(block_dst, value, result_index);
            }
            for (i = 0; i < block_dst->result_count; i++) {
                PUSH(values[i], block_dst->result_types[i]);
            }
            wasm_runtime_free(values);
            values = NULL;
        }

        /* Condition jump to end block */
        BUILD_COND_BR(value_cmp, block_dst->llvm_end_block, llvm_else_block);

        /* Move builder to else block */
        SET_BUILDER_POS(llvm_else_block);
    }

    return true;
fail:
    if (values)
        wasm_runtime_free(values);
    return false;
}

bool
aot_compile_op_br_on_null(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                          uint32 br_depth, uint8 **p_frame_ip)
{
    LLVMValueRef gc_obj, value_cmp;

    if (!commit_gc_and_check_suspend_flags(comp_ctx, func_ctx, br_depth)) {
        return false;
    }

    POP_GC_REF(gc_obj);

    if (!(value_cmp =
              LLVMBuildIsNull(comp_ctx->builder, gc_obj, "cmp_gc_obj"))) {
        aot_set_last_error("llvm build isnull failed.");
        goto fail;
    }

    if (!compile_gc_cond_br(comp_ctx, func_ctx, br_depth, value_cmp)) {
        goto fail;
    }

    PUSH_GC_REF(gc_obj);
    return true;
fail:
    return false;
}

bool
aot_compile_op_br_on_non_null(AOTCompContext *comp_ctx,
                              AOTFuncContext *func_ctx, uint32 br_depth,
                              uint8 **p_frame_ip)
{
    LLVMValueRef gc_obj, value_cmp;

    if (!commit_gc_and_check_suspend_flags(comp_ctx, func_ctx, br_depth)) {
        return false;
    }

    GET_GC_REF_FROM_STACK(gc_obj);

    if (!(value_cmp =
              LLVMBuildIsNotNull(comp_ctx->builder, gc_obj, "cmp_gc_obj"))) {
        aot_set_last_error("llvm build isnotnull failed.");
        goto fail;
    }

    if (!compile_gc_cond_br(comp_ctx, func_ctx, br_depth, value_cmp)) {
        goto fail;
    }

    POP_GC_REF(gc_obj);
    return true;
fail:
    return false;
}

bool
aot_compile_op_br_on_cast(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                          int32 heap_type, bool nullable, bool br_on_fail,
                          uint32 br_depth, uint8 **p_frame_ip)
{
    LLVMValueRef gc_obj, is_null, castable, not_castable, br_if_phi;
    LLVMBasicBlockRef block_curr, block_non_null, block_br_if;

    if (!commit_gc_and_check_suspend_flags(comp_ctx, func_ctx, br_depth)) {
        return false;
    }

    GET_GC_REF_FROM_STACK(gc_obj);

    block_curr = CURR_BLOCK();

    CREATE_BLOCK(block_non_null, "obj_non_null");
    MOVE_BLOCK_AFTER_CURR(block_non_null);
    CREATE_BLOCK(block_br_if, "br_if");
    MOVE_BLOCK_AFTER(block_br_if, block_non_null);

    SET_BUILDER_POS(block_br_if);
    if (!(br_if_phi =
              LLVMBuildPhi(comp_ctx->builder, INT1_TYPE, "br_if_phi"))) {
        aot_set_last_error("llvm build phi failed.");
        goto fail;
    }

    SET_BUILDER_POS(block_curr);

    if (!(is_null = LLVMBuildIsNull(comp_ctx->builder, gc_obj, "is_null"))) {
        aot_set_last_error("llvm build isnull failed.");
        goto fail;
    }

    BUILD_COND_BR(is_null, block_br_if, block_non_null);

    if ((!br_on_fail && nullable) || (br_on_fail && !nullable)) {
        LLVMAddIncoming(br_if_phi, &I1_ONE, &block_curr, 1);
    }
    else { /* (!br_on_fail && !nullable) || (br_on_fail && nullable)) */
        LLVMAddIncoming(br_if_phi, &I1_ZERO, &block_curr, 1);
    }

    SET_BUILDER_POS(block_non_null);
    if (heap_type >= 0) {
        if (!aot_call_aot_obj_is_instance_of(comp_ctx, func_ctx, gc_obj,
                                             I32_CONST(heap_type), &castable))
            goto fail;
    }
    else {
        if (!aot_call_wasm_obj_is_type_of(comp_ctx, func_ctx, gc_obj,
                                          I32_CONST(heap_type), &castable))
            goto fail;
    }

    if (!br_on_fail) {
        if (!(castable = LLVMBuildICmp(comp_ctx->builder, LLVMIntNE, castable,
                                       I8_ZERO, "castable"))) {
            aot_set_last_error("llvm build icmp failed.");
            return false;
        }
        LLVMAddIncoming(br_if_phi, &castable, &block_non_null, 1);
    }
    else {
        if (!(not_castable = LLVMBuildICmp(comp_ctx->builder, LLVMIntEQ,
                                           castable, I8_ZERO, "castable"))) {
            aot_set_last_error("llvm build icmp failed.");
            return false;
        }
        LLVMAddIncoming(br_if_phi, &not_castable, &block_non_null, 1);
    }
    BUILD_BR(block_br_if);

    SET_BUILDER_POS(block_br_if);
    if (!compile_gc_cond_br(comp_ctx, func_ctx, br_depth, br_if_phi)) {
        goto fail;
    }

    return true;
fail:
    return false;
}

#endif /* End of WASM_ENABLE_GC != 0 */

#if WASM_ENABLE_EXCE_HANDLING != 0
/* M6 task 2: exception-handling opcode codegen (frame-based unwind; mirrors the
   interpreter, not LLVM landingpads). The try scaffold (entry block + a
   catch-dispatch block) is emitted by aot_compile_op_block for LABEL_TYPE_TRY;
   the functions below emit throw/catch/rethrow/delegate. An in-flight exception
   is recorded in per-function entry-block storage (see AOTFuncContext.exce_*):
   the thrown tag index and a byte buffer of its param values, so a catch can
   read what a throw wrote. Currently the INTRA-function path (throw + catch in
   the same function) is implemented; cross-function propagation (per-call
   exception-pending checks + a runtime pending flag) and rethrow/delegate are
   the next increments (route_a/M6_EH_AOT_PLAN.md) and fail with a NAMED error
   rather than silently mis-compiling. */

/* Lazily create the entry-block exception storage so it dominates every throw
   and catch in the function. */
static bool
aot_ensure_exce_storage(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx)
{
    WASMModule *module = comp_ctx->comp_data->wasm_module;
    LLVMBuilderRef builder = comp_ctx->builder;
    LLVMBasicBlockRef cur_block, entry_block;
    LLVMValueRef first_instr;
    uint32 i, j, sz, max_size = 0;
    uint32 tag_total = module->import_tag_count + module->tag_count;

    if (func_ctx->exce_tag_alloca)
        return true;

    for (i = 0; i < tag_total; i++) {
        WASMFuncType *tt = module->tags[i]->tag_type;
        sz = 0;
        for (j = 0; j < tt->param_count; j++)
            sz += wasm_value_type_size_internal(
                tt->types[j], (uint8)comp_ctx->pointer_size);
        if (sz > max_size)
            max_size = sz;
    }
    if (max_size == 0)
        max_size = 4;
    func_ctx->exce_values_size = max_size;

    cur_block = LLVMGetInsertBlock(builder);
    entry_block = LLVMGetEntryBasicBlock(func_ctx->func);
    first_instr = LLVMGetFirstInstruction(entry_block);
    if (first_instr)
        LLVMPositionBuilderBefore(builder, first_instr);
    else
        LLVMPositionBuilderAtEnd(builder, entry_block);

    func_ctx->exce_tag_alloca = LLVMBuildAlloca(builder, I32_TYPE, "exce_tag");
    func_ctx->exce_values_alloca =
        LLVMBuildArrayAlloca(builder, INT8_TYPE, I32_CONST(max_size),
                             "exce_values");
    LLVMPositionBuilderAtEnd(builder, cur_block);

    if (!func_ctx->exce_tag_alloca || !func_ctx->exce_values_alloca) {
        aot_set_last_error("llvm build alloca failed for exception storage.");
        return false;
    }
    return true;
}

/* Store `value` (of wasm type value_type) at byte `offset` in the exception
   values buffer. */
static bool
aot_store_exce_value(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                     uint32 offset, LLVMValueRef value, uint8 value_type)
{
    LLVMValueRef idx = I32_CONST(offset), ptr, tptr;
    LLVMTypeRef llvm_type = TO_LLVM_TYPE(value_type);

    if (!(ptr = LLVMBuildInBoundsGEP2(comp_ctx->builder, INT8_TYPE,
                                      func_ctx->exce_values_alloca, &idx, 1,
                                      "exce_val_ptr"))
        || !(tptr = LLVMBuildBitCast(comp_ctx->builder, ptr,
                                     LLVMPointerType(llvm_type, 0),
                                     "exce_val_tptr"))
        || !LLVMBuildStore(comp_ctx->builder, value, tptr)) {
        aot_set_last_error("llvm build store exception value failed.");
        return false;
    }
    return true;
}

bool
aot_compile_op_throw(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                     uint32 tag_index, uint8 **p_frame_ip)
{
    WASMModule *module = comp_ctx->comp_data->wasm_module;
    WASMFuncType *tag_type;
    AOTBlock *try_block;
    LLVMBasicBlockRef target;
    LLVMValueRef value, tag_val;
    uint32 *offsets = NULL;
    uint32 i, off = 0, param_count;
    uint8 param_type;
    bool ret = false;

    if (tag_index >= module->import_tag_count + module->tag_count) {
        aot_set_last_error("invalid tag index in throw.");
        return false;
    }
    tag_type = module->tags[tag_index]->tag_type;
    param_count = tag_type->param_count;

    if (!aot_ensure_exce_storage(comp_ctx, func_ctx))
        return false;

    if (param_count > 0) {
        if (!(offsets = wasm_runtime_malloc((uint32)sizeof(uint32) * param_count))) {
            aot_set_last_error("allocate memory failed.");
            return false;
        }
        for (i = 0; i < param_count; i++) {
            offsets[i] = off;
            off += wasm_value_type_size_internal(tag_type->types[i],
                                                 (uint8)comp_ctx->pointer_size);
        }
        /* the last param is on top of the stack; pop in reverse */
        for (i = param_count; i > 0; i--) {
            param_type = tag_type->types[i - 1];
            POP(value, param_type);
            if (!aot_store_exce_value(comp_ctx, func_ctx, offsets[i - 1], value,
                                      param_type))
                goto fail;
        }
    }

    tag_val = I32_CONST(tag_index);
    if (!LLVMBuildStore(comp_ctx->builder, tag_val, func_ctx->exce_tag_alloca)) {
        aot_set_last_error("llvm build store failed.");
        goto fail;
    }

    /* Branch to the innermost enclosing try's catch dispatch. If there is no
       enclosing try in this function the exception is uncaught here: for now go
       to the function's got_exception epilogue (cross-function propagation via a
       runtime pending flag + per-call checks is the next increment). */
    try_block = func_ctx->block_stack.block_list_end;
    while (try_block
           && (try_block->label_type != LABEL_TYPE_TRY || try_block->in_handler))
        try_block = try_block->prev;

    if (try_block) {
        /* Branch to this try's catch dispatch. The post-throw block is now
           terminated and dead; skip forward like a br so any dead code between
           the throw and the try's first catch is not emitted into it.
           handle_next_reachable_block stops at the enclosing try (see its
           LABEL_TYPE_TRY case) and resumes parsing at the first catch. */
        BUILD_BR(try_block->llvm_catch_dispatch_block);
        ret = aot_handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
    }
    else {
        /* Uncaught in this function -- TODO(M6): propagate to the caller via a
           runtime exception-pending flag; for now (intra-function EH only) it is
           unreachable. Then skip the dead code after, like a return. */
        if (!LLVMBuildUnreachable(comp_ctx->builder)) {
            aot_set_last_error("llvm build unreachable failed.");
            goto fail;
        }
        ret = aot_handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
    }
fail:
    if (offsets)
        wasm_runtime_free(offsets);
    return ret;
}

bool
aot_compile_op_rethrow(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                       uint32 relative_depth, uint8 **p_frame_ip)
{
    /* Re-throw the in-flight exception (its tag+values are still in the exce
       storage) to the handlers enclosing the try at relative_depth. In this
       model a catch handler runs with its TRY block on the stack, so count TRY
       blocks: relative_depth 0 is the innermost. Re-propagate to that try's
       enclosing try dispatch, or unreachable if uncaught (cross-function TODO). */
    /* relative_depth is a control-label depth (like br): count ALL enclosing
       frames, not only trys. The frame at that depth is the try whose handler we
       are re-throwing from (validation guarantees it is a TRY). Re-propagate the
       in-flight exception to the handlers enclosing THAT try -- its nearest
       enclosing try that we are not already handling (skip in_handler, as
       op_throw does). */
    AOTBlock *target = func_ctx->block_stack.block_list_end;
    AOTBlock *outer;
    uint32 d = relative_depth;

    while (d > 0 && target) {
        target = target->prev;
        d--;
    }
    outer = target ? target->prev : NULL;
    while (outer && (outer->label_type != LABEL_TYPE_TRY || outer->in_handler))
        outer = outer->prev;
    if (outer) {
        BUILD_BR(outer->llvm_catch_dispatch_block);
    }
    else if (!LLVMBuildUnreachable(comp_ctx->builder)) {
        aot_set_last_error("llvm build unreachable failed.");
        return false;
    }
    return aot_handle_next_reachable_block(comp_ctx, func_ctx, p_frame_ip);
fail:
    return false;
}

bool
aot_compile_op_catch(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                     uint32 tag_index)
{
    WASMModule *module = comp_ctx->comp_data->wasm_module;
    WASMFuncType *tag_type;
    AOTBlock *try_block = func_ctx->block_stack.block_list_end;
    LLVMBasicBlockRef cur_block, handler_block, next_block;
    LLVMValueRef tag_val, cmp, value, idx, ptr, tptr;
    uint32 i, off = 0;
    uint8 ptype;
    char name[32];

    if (!try_block || try_block->label_type != LABEL_TYPE_TRY) {
        aot_set_last_error("catch not directly in a try block.");
        return false;
    }
    if (tag_index >= module->import_tag_count + module->tag_count) {
        aot_set_last_error("invalid tag index in catch.");
        return false;
    }
    tag_type = module->tags[tag_index]->tag_type;

    /* Ensure the exception storage exists: a function may CATCH without itself
       THROWing (the exception was thrown in a callee), so the storage was not
       created by a throw here. (NOTE: cross-function reads of a per-function
       alloca are not yet correct -- that needs the runtime exception state; this
       just avoids a NULL deref so the module compiles. See M6_EH_AOT_PLAN.md.) */
    if (!aot_ensure_exce_storage(comp_ctx, func_ctx))
        return false;

    /* The preceding section (try body or previous catch handler) falls through
       to the try end when its block is still live; if it ended in a branch/
       return/throw the block is already terminated and contributes no result. */
    cur_block = LLVMGetInsertBlock(comp_ctx->builder);
    if (cur_block && !LLVMGetBasicBlockTerminator(cur_block)) {
        if (!try_block->llvm_end_block) {
            format_block_name(name, sizeof(name), try_block->block_index,
                              try_block->label_type, LABEL_END);
            CREATE_BLOCK(try_block->llvm_end_block, name);
        }
        CREATE_RESULT_VALUE_PHIS(try_block);
        for (i = 0; i < try_block->result_count; i++) {
            uint32 ri = try_block->result_count - 1 - i;
            POP(value, try_block->result_types[ri]);
            ADD_TO_RESULT_PHIS(try_block, value, ri);
        }
        BUILD_BR(try_block->llvm_end_block);
    }

    /* Emit this catch's tag test at the dispatch-chain point (the first catch
       uses the try's catch-dispatch block; later catches use the previous
       catch's mismatch block). */
    SET_BUILDER_POS(try_block->llvm_catch_next_block);
    CREATE_BLOCK(handler_block, "catch_handler");
    CREATE_BLOCK(next_block, "catch_next");
    if (!(tag_val = LLVMBuildLoad2(comp_ctx->builder, I32_TYPE,
                                   func_ctx->exce_tag_alloca, "exce_tag"))) {
        aot_set_last_error("llvm build load failed.");
        return false;
    }
    if (!(cmp = LLVMBuildICmp(comp_ctx->builder, LLVMIntEQ, tag_val,
                              I32_CONST(tag_index), "tag_match"))) {
        aot_set_last_error("llvm build icmp failed.");
        return false;
    }
    BUILD_COND_BR(cmp, handler_block, next_block);
    try_block->llvm_catch_next_block = next_block;

    /* From here on we emit this try's handler body: a throw inside it must
       propagate to the ENCLOSING try, not be re-caught here. */
    try_block->in_handler = true;

    /* Handler: reset the try's value stack to empty, then push the exception's
       param values (loaded from the values buffer) for the handler body. */
    aot_value_stack_destroy(comp_ctx, &try_block->value_stack);
    SET_BUILDER_POS(handler_block);
    for (i = 0; i < tag_type->param_count; i++) {
        ptype = tag_type->types[i];
        idx = I32_CONST(off);
        if (!(ptr = LLVMBuildInBoundsGEP2(comp_ctx->builder, INT8_TYPE,
                                          func_ctx->exce_values_alloca, &idx, 1,
                                          "ev_ptr"))
            || !(tptr = LLVMBuildBitCast(comp_ctx->builder, ptr,
                                         LLVMPointerType(TO_LLVM_TYPE(ptype), 0),
                                         "ev_tptr"))
            || !(value = LLVMBuildLoad2(comp_ctx->builder, TO_LLVM_TYPE(ptype),
                                        tptr, "ev"))) {
            aot_set_last_error("llvm build load exception value failed.");
            return false;
        }
        PUSH(value, ptype);
        off += wasm_value_type_size_internal(ptype,
                                             (uint8)comp_ctx->pointer_size);
    }

    return true;
fail:
    return false;
}

bool
aot_compile_op_catch_all(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx)
{
    AOTBlock *try_block = func_ctx->block_stack.block_list_end;
    LLVMBasicBlockRef cur_block, handler_block;
    LLVMValueRef value;
    uint32 i;
    char name[32];

    if (!try_block || try_block->label_type != LABEL_TYPE_TRY) {
        aot_set_last_error("catch_all not directly in a try block.");
        return false;
    }
    if (!aot_ensure_exce_storage(comp_ctx, func_ctx))
        return false;

    /* Preceding section (try body or a prior catch handler) falls through to the
       try end if its block is still live. */
    cur_block = LLVMGetInsertBlock(comp_ctx->builder);
    if (cur_block && !LLVMGetBasicBlockTerminator(cur_block)) {
        if (!try_block->llvm_end_block) {
            format_block_name(name, sizeof(name), try_block->block_index,
                              try_block->label_type, LABEL_END);
            CREATE_BLOCK(try_block->llvm_end_block, name);
        }
        CREATE_RESULT_VALUE_PHIS(try_block);
        for (i = 0; i < try_block->result_count; i++) {
            uint32 ri = try_block->result_count - 1 - i;
            POP(value, try_block->result_types[ri]);
            ADD_TO_RESULT_PHIS(try_block, value, ri);
        }
        BUILD_BR(try_block->llvm_end_block);
    }

    /* catch_all matches any exception: unconditional branch to the handler. It
       exposes no params. Since it catches everything, there is no mismatch edge
       to re-propagate -- clear catch_next so finalization skips it. */
    SET_BUILDER_POS(try_block->llvm_catch_next_block);
    CREATE_BLOCK(handler_block, "catch_all_handler");
    BUILD_BR(handler_block);
    try_block->llvm_catch_next_block = NULL;

    /* Emitting this try's handler: a throw inside it propagates to the enclosing
       try, not back into this one. */
    try_block->in_handler = true;

    aot_value_stack_destroy(comp_ctx, &try_block->value_stack);
    SET_BUILDER_POS(handler_block);
    return true;
fail:
    return false;
}

bool
aot_compile_op_delegate(AOTCompContext *comp_ctx, AOTFuncContext *func_ctx,
                        uint32 relative_depth, uint8 **p_frame_ip)
{
    (void)comp_ctx;
    (void)func_ctx;
    (void)relative_depth;
    (void)p_frame_ip;
    aot_set_last_error("aot: WASM_OP_DELEGATE codegen not yet implemented (M6 task 2)");
    return false;
}
#endif /* WASM_ENABLE_EXCE_HANDLING != 0 */
