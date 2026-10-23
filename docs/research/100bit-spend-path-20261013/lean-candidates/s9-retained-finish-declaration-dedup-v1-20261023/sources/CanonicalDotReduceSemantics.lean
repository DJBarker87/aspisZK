import AspisR1CanonicalDotFinish.Funs
import ExtractedCurrentReducer
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CanonicalDotFinish.Proof
open AspisR1.ExtractedCurrentReducer AspisR1.ExtractedCurrentReducerOps
open AspisV8R17.RawReducer

def reduceBeforeCast (x : U64) : Result U32 := do
  let first ← foldExecution x
  let second ← foldExecution first
  if P ≤ second.val then
    let remainder ← UScalar.sub second mask64
    ok (UScalar.cast .U32 remainder)
  else ok (UScalar.cast .U32 second)

theorem canonical_reduce_source_eq (x : U64) : canonical.reduce x = reduceBeforeCast x := by
  simp only [canonical.reduce,canonical.P,reduceBeforeCast,foldExecution,
    mask64,mask32,lift,bind_tc_ok,bind_assoc_eq]
  rfl

theorem reduceBeforeCast_mod (x : U64) :
    ∃ out : U32, reduceBeforeCast x = .ok out ∧ out.val=x.val%P ∧ out.val<P := by
  obtain ⟨first,hfirst,hfv⟩ := foldExecution_success x
  obtain ⟨second,hsecond,hsv⟩ := foldExecution_success first
  have hval : second.val=foldBits (foldBits x.val) := by rw [hsv,hfv]
  have hbound : second.val<2^32 := by
    rw [hval]
    exact second_fold_lt_two_pow32 x.val x.bv.isLt
  have hraw : rawReduceU64 x.val=condSubP second.val := by
    rw [rawReduceU64,second_fold_cast_exact x.val x.bv.isLt,←hval]
  have hmod := rawReduceU64_eq_mod_nat x.val x.bv.isLt
  have hcanon := rawReduceU64_canonical x.val x.bv.isLt
  by_cases h : P ≤ second.val
  · obtain ⟨rem,hrem,hrv⟩ := sub_success second mask64 (by simpa only [mask64_value] using h)
    have hrb : rem.val<2^32 := by rw [hrv,mask64_value];omega
    have hout : (UScalar.cast .U32 rem).val=rawReduceU64 x.val := by
      rw [narrow_exact rem hrb,hrv,mask64_value,hraw,condSubP,if_pos h]
    exact ⟨UScalar.cast .U32 rem,
      by simp only [reduceBeforeCast,hfirst,hsecond,bind_tc_ok,h,if_pos,hrem],
      hout.trans hmod,by rw [hout];exact hcanon⟩
  · have hout : (UScalar.cast .U32 second).val=rawReduceU64 x.val := by
      rw [narrow_exact second hbound,hraw,condSubP,if_neg h]
    exact ⟨UScalar.cast .U32 second,
      by simp only [reduceBeforeCast,hfirst,hsecond,bind_tc_ok,h,if_false],
      hout.trans hmod,by rw [hout];exact hcanon⟩

theorem canonical_reduce_mod (x : U64) :
    ∃ out : U32, canonical.reduce x = .ok out ∧ out.val=x.val%P ∧ out.val<P := by
  rw [canonical_reduce_source_eq]
  exact reduceBeforeCast_mod x

#print axioms canonical_reduce_source_eq
#print axioms reduceBeforeCast_mod
#print axioms canonical_reduce_mod
end AspisR1CanonicalDotFinish.Proof
