import FJa_TensorMeaning
import R0P.SemDeg
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_WeightBits
open FIv_NativeValue (K)
/-- Literal list tensor equals the already retained bit-weight definition. -/
theorem value (cs : List K) (j : Nat) :
    FJa_TensorMeaning.weight cs j=R0P.SemDegree.bitWeight cs.length
      (fun i=>cs[i.val]) j := by
  induction cs with
  | nil => simp only [FJa_TensorMeaning.weight,R0P.SemDegree.bitWeight,Fin.prod_univ_zero]
  | cons c cs ih =>
    unfold FJa_TensorMeaning.weight
    rw [R0P.SemDegree.bitWeight,Fin.prod_univ_succ]
    simp only [List.length_cons,Fin.val_zero,Fin.val_succ,List.getElem_cons_zero,List.getElem_cons_succ]
    have exp : cs.length+1-1-0=cs.length := by omega
    rw [exp]
    have factor : R0P.SemDegree.bitFactor (j.testBit cs.length) c=
        (if j/2^cs.length%2=0 then 1-c else c) := by
      rcases Nat.mod_two_eq_zero_or_one (j/2^cs.length) with h | h <;>
        simp [Nat.testBit_eq_decide_div_mod_eq,R0P.SemDegree.bitFactor,h]
    rw [factor,ih]
    congr 1
    unfold R0P.SemDegree.bitWeight
    apply Finset.prod_congr rfl
    intro i _
    congr 2
    omega
#print axioms value
end AspisR1.FJa_WeightBits
end
