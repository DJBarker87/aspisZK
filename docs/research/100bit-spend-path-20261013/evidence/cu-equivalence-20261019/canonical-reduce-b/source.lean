import AspisR1CanonicalDots.Funs
import CuSavingsRhoValue
set_option autoImplicit false
namespace AspisR1.CuSavingsCanonicalDotsReduce
open Aeneas Aeneas.Std Result AspisR1CanonicalDots
open AspisV8R17.RawReducer
open ExtractedCurrentReducerOps ExtractedCurrentReducer

theorem reduce_source (x : U64) :
    ∃ out : U32,new_pairing.canonical.reduce x = .ok out ∧
      out.val=x.val%P ∧ out.val<P := by
  obtain ⟨first,hfirst,hfv⟩ := foldExecution_success x
  obtain ⟨second,hsecond,hsv⟩ := foldExecution_success first
  rw [hfv] at hsv
  have hsecondBound : second.val < 2^32 := by
    rw [hsv]
    exact second_fold_lt_two_pow32 x.val x.bv.isLt
  have factor : new_pairing.canonical.reduce x = (do
      let first ← foldExecution x
      let second ← foldExecution first
      if P≤second.val then
        do let out ← UScalar.sub second mask64
           .ok (UScalar.cast .U32 out)
      else .ok (UScalar.cast .U32 second)) := by
    simp only [new_pairing.canonical.reduce,new_pairing.canonical.P,
      foldExecution,mask64,mask32,lift,bind_tc_ok,bind_assoc_eq]
    rfl
  have hraw : rawReduceU64 x.val=condSubP second.val := by
    rw [rawReduceU64,second_fold_cast_exact x.val x.bv.isLt,hsv]
  have hcanon : condSubP second.val<P := by
    rw [← hraw]
    exact rawReduceU64_canonical x.val x.bv.isLt
  have hmod : condSubP second.val=x.val%P := by
    rw [← hraw]
    exact rawReduceU64_eq_mod_nat x.val x.bv.isLt
  rw [factor,hfirst,hsecond]
  simp only [bind_tc_ok]
  by_cases h : P≤second.val
  · obtain ⟨reduced,hr,hrv⟩ := sub_success second mask64
      (by simpa only [mask64_value] using h)
    have hrbound : reduced.val<2^32 := by rw [hrv,mask64_value];omega
    have hv : (UScalar.cast .U32 reduced).val=reduced.val := by
      rw [cast_value,Nat.mod_eq_of_lt hrbound]
    refine ⟨UScalar.cast .U32 reduced,?_,?_,?_⟩
    · rw [if_pos h,hr];rfl
    · rw [hv,hrv,mask64_value]
      simpa only [condSubP,if_pos h] using hmod
    · rw [hv,hrv,mask64_value]
      simpa only [condSubP,if_pos h] using hcanon
  · have hv : (UScalar.cast .U32 second).val=second.val := by
      rw [cast_value,Nat.mod_eq_of_lt hsecondBound]
    refine ⟨UScalar.cast .U32 second,by rw [if_neg h],?_,?_⟩
    · rw [hv]
      simpa only [condSubP,if_neg h] using hmod
    · rw [hv]
      simpa only [condSubP,if_neg h] using hcanon

theorem reduce_returns (x : U64) :
    new_pairing.canonical.reduce x=.ok (CuSavingsRhoValue.canonicalWord x) := by
  obtain ⟨out,hr,hv,_⟩ := reduce_source x
  have heq : out=CuSavingsRhoValue.canonicalWord x := UScalar.eq_of_val_eq hv
  simpa only [heq] using hr

theorem old_reduce_eq (x : U64) :
    old_pairing.canonical.reduce x=new_pairing.canonical.reduce x := by
  simp only [old_pairing.canonical.reduce,new_pairing.canonical.reduce,
    old_pairing.canonical.P,new_pairing.canonical.P]

theorem reduce_eq_runtime (x : U64) :
    new_pairing.canonical.reduce x=AspisR1CuRho.field.M31.reduce_u64 x := by
  rw [reduce_returns,CuSavingsRhoValue.reducer_returns]

#print axioms reduce_source
#print axioms reduce_returns
#print axioms old_reduce_eq
#print axioms reduce_eq_runtime
end AspisR1.CuSavingsCanonicalDotsReduce
