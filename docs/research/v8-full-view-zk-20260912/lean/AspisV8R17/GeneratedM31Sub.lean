import AspisV8R17.GeneratedM31Mul

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::sub"]
def aspis_core.field.M31.sub
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let i ← self + aspis_core.field.P
  let s ← i - rhs
  if s >= aspis_core.field.P
  then let s1 ← s - aspis_core.field.P
       ok s1
  else ok s
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedM31Sub
open Aeneas.Std V7Tag73CurrentHelpersOpaque UnsignedReducerOps UnsignedCoreSlice
open RawReducer

theorem source_P_value : aspis_core.field.P.val = P := by
  rw [aspis_core.field.P]
  rfl

def finishSub (n : U32) : Result U32 :=
  if n ≥ aspis_core.field.P then do
    let r ← UScalar.sub n aspis_core.field.P
    .ok r
  else .ok n

theorem finishSub_mod (n : U32) (hn : n.val < 2*P) :
    ∃ r : U32, finishSub n = .ok r ∧ r.val = n.val % P ∧ r.val < P := by
  have branch : (n ≥ aspis_core.field.P) ↔ P ≤ n.val := by
    change aspis_core.field.P.val ≤ n.val ↔ P ≤ n.val
    rw [source_P_value]
  by_cases h : P ≤ n.val
  · obtain ⟨r, hr, hv⟩ := sub_success n aspis_core.field.P (by rw [source_P_value]; exact h)
    rw [source_P_value] at hv
    have small : n.val-P < P := by omega
    refine ⟨r, ?_, ?_, by rw [hv]; exact small⟩
    · simp only [finishSub, branch, h, if_pos, hr, bind_tc_ok]
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt small]
      exact hv
  · have small : n.val < P := Nat.lt_of_not_ge h
    exact ⟨n, by simp only [finishSub, branch, h, if_false],
      (Nat.mod_eq_of_lt small).symm, small⟩

theorem generated_sub_mod (x y : aspis_core.field.M31)
    (hx : x.val < P) (hy : y.val < P) :
    ∃ r : aspis_core.field.M31, aspis_core.field.M31.sub x y = .ok r ∧
      r.val = (x.val+P-y.val) % P ∧ r.val < P := by
  have p : P = 2147483647 := rfl
  have hbound : x.val + aspis_core.field.P.val < 2^32 := by
    rw [source_P_value]
    omega
  have hadd : ∃ i : U32, UScalar.add x aspis_core.field.P = .ok i ∧
      i.val = x.val + aspis_core.field.P.val := tryMk_success _ hbound
  obtain ⟨i, hi, hiv⟩ := hadd
  rw [source_P_value] at hiv
  obtain ⟨n, hn, hnv⟩ := sub_success i y (by rw [hiv]; omega)
  rw [hiv] at hnv
  obtain ⟨r, hr, hrv, hrc⟩ := finishSub_mod n (by rw [hnv]; omega)
  refine ⟨r, ?_, ?_, hrc⟩
  · change (do
      let i ← UScalar.add x aspis_core.field.P
      let n ← UScalar.sub i y
      finishSub n) = Result.ok r
    simp only [hi, hn, bind_tc_ok, hr]
  · simpa only [hnv] using hrv

#print axioms source_P_value
#print axioms finishSub_mod
#print axioms generated_sub_mod
end AspisV8R17.GeneratedM31Sub
