import AspisR357BatchZeroPredicateRaw
import AspisV8R19.ComplexBaseExecution

/-! Exact source zero predicate and its preserved closure state. This is not
an iterator/any execution theorem or a proof of the original enclosing guard. -/
set_option autoImplicit false
namespace AspisV8R19.R358BatchZeroPredicate
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase (M31Exact)
open AspisV8R19.ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast)
open AspisR357BatchZeroPredicateRaw.circle_norm.joined_inverse.line_norm.r110_norm
open AspisR278PrivateInverseRaw.circle_norm.joined_inverse.line_norm.r110_norm (B.ZERO)
noncomputable section

theorem encodeBase_injective (x y : M31Exact)
    (h : encodeBase x = encodeBase y) : x = y := by
  have hv := congrArg (fun w : U32 => (w.val : M31Exact)) h
  simpa only [encodeBase_cast] using hv

theorem encodeBase_eq_source_zero (x : M31Exact) :
    encodeBase x = B.ZERO ↔ x = 0 := by
  have hzero : B.ZERO = encodeBase (0 : M31Exact) := by
    apply UScalar.eq_of_val_eq
    simp only [B.ZERO, encodeBase_val, ZMod.val_zero]
  rw [hzero]
  constructor
  · exact encodeBase_injective x 0
  · intro hx
    rw [hx]

theorem call_mut_all_words (c : batch.closure) (w : U32) :
    batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut c w =
      .ok (decide (w = B.ZERO), c) := by
  simp only [batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut,
    B.Insts.CoreCmpPartialEqB.eq, bind_tc_ok]

theorem call_mut_encoded (c : batch.closure) (x : M31Exact) :
    batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut c (encodeBase x) =
      .ok (decide (x = 0), c) := by
  rw [call_mut_all_words]
  simp only [encodeBase_eq_source_zero]

theorem call_once_encoded (c : batch.closure) (x : M31Exact) :
    batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool.call_once c (encodeBase x) =
      .ok (decide (x = 0)) := by
  simp only [batch.closure.Insts.CoreOpsFunctionFnOnceTupleSharedBBool.call_once,
    call_mut_encoded, bind_tc_ok]

theorem call_mut_encoded_nonzero (c : batch.closure) (x : M31Exact) (hx : x ≠ 0) :
    batch.closure.Insts.CoreOpsFunctionFnMutTupleSharedBBool.call_mut c (encodeBase x) =
      .ok (false, c) := by
  rw [call_mut_encoded]
  simp only [decide_eq_false hx]

#print axioms encodeBase_injective
#print axioms encodeBase_eq_source_zero
#print axioms call_mut_all_words
#print axioms call_mut_encoded
#print axioms call_once_encoded
#print axioms call_mut_encoded_nonzero
end
end AspisV8R19.R358BatchZeroPredicate
