import CuSavingsRetainedCompositionDotsPrefixSource
import CuSavingsPrefix
import CuSavingsRetainedCompositionPrefixSlot

/-! Relational execution of the complete emitted kernels on the same bytes.
This transports actual array/slice access, loops and closure state under
arbitrary shared arithmetic operations, including their failures/divergence.
The longer-query prefix-insensitivity and std array-builder admission remain
separate obligations; this file does not claim whole-candidate closure. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1.CuSavingsRetainedCompositionPrefixSameBytes
open Aeneas Aeneas.Std Result AspisR1RetainedDots
open CuSavingsArrayBuilder
def forget (state : prefix_new_dots.four_dots.closure) : new_dots.four_dots.closure :=
  (state.1.to_slice,state.2)

variable [Shared]

theorem base_loop_same (iter : core.ops.range.Range Usize)
    (bytes : Array U8 608#usize) (gamma : Array field.wide_exact.WideExact 29#usize)
    (slot : Usize) (sums : Array U64 8#usize) :
    prefix_new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
        iter bytes gamma slot sums =
      new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0
        iter bytes.to_slice gamma slot sums := by
  rfl

theorem batches_same
    (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (bytes : Array U8 608#usize) (gamma : Array field.wide_exact.WideExact 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) :
    prefix_new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        iter bytes gamma slot limbs =
      new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0
        iter bytes.to_slice gamma slot limbs := by
  rfl

theorem tail_same (iter : core.ops.range.Range Usize)
    (bytes : Array U8 608#usize) (gamma : Array field.wide_exact.WideExact 29#usize)
    (slot : Usize) (tail : fast_pairing.EbyKDot) :
    prefix_new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
        iter bytes gamma slot tail =
      new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1
        iter bytes.to_slice gamma slot tail := by
  rfl

theorem callback_transport (state : prefix_new_dots.four_dots.closure) (slot : Usize) :
    remap (fun (value,state1) => (value,forget state1))
      (prefix_new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        state slot) =
      new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
        (forget state) slot := by
  rcases state with ⟨bytes,gamma⟩
  rw [show forget (bytes,gamma) = (bytes.to_slice,gamma) from rfl]
  rw [CuSavingsRetainedCompositionPrefixSlot.new_factor,CuSavingsRetainedCompositionPrefixSlot.old_factor]
  exact (CuSavingsRetainedCompositionPrefixSlot.naturality _ _ _ _ _).trans (by rfl)

theorem construct_same (state : prefix_new_dots.four_dots.closure) :
    core.array.from_fn 4#usize
        prefix_new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact state =
      core.array.from_fn 4#usize
        new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
        (forget state) := by
  apply build_naturality _ _ forget
  exact callback_transport

theorem source_same_bytes (bytes : Array U8 608#usize)
    (gamma : Array field.wide_exact.WideExact 29#usize) :
    prefix_new_dots.four_dots bytes.to_slice gamma = new_dots.four_dots bytes.to_slice gamma := by
  have hb : bytes.val.length = 608 := by
    simpa only [show (608#usize).val = 608 by scalar_tac] using bytes.property
  have hlen : 608 ≤ bytes.to_slice.val.length := by
    simpa only [Array.to_slice,hb] using Nat.le_refl 608
  have hprefix : CuSavingsPrefix.prefixArray bytes.to_slice hlen = bytes := by
    apply Subtype.ext
    change bytes.val.take 608 = bytes.val
    simpa only [hb] using (List.take_length (l := bytes.val))
  have hp := CuSavingsPrefix.source_success bytes.to_slice hlen
  rw [hprefix] at hp
  have expand : prefix_new_dots.four_dots bytes.to_slice gamma =
      (do let fixed ← AspisR1CuPrefix.fixed_prefix bytes.to_slice
          core.array.from_fn 4#usize
            prefix_new_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
            (fixed,gamma)) := by
    simp only [prefix_new_dots.four_dots,AspisR1CuPrefix.fixed_prefix,bind_assoc_eq]
  rw [expand,hp]
  simp only [bind_tc_ok,new_dots.four_dots]
  exact construct_same (bytes,gamma)

#print axioms base_loop_same
#print axioms batches_same
#print axioms tail_same
#print axioms callback_transport
#print axioms construct_same
#print axioms source_same_bytes
end AspisR1.CuSavingsRetainedCompositionPrefixSameBytes
