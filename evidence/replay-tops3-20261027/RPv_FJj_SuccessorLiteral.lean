import RPv_FJj_SuccessorLiteralStep
import RPv_FJj_SuccessorOrder
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorLiteral
variable {K : Type} [Field K]

theorem suffix (z : Fin 10 → K) (e : Nat) (he : e≤10) :
    (FJj_SuccessorModel.eval z e (FJj_SuccessorLiteralStep.state z e)).2=
      R0P.SemSource.successorPoint z := by
  induction e with
  | zero =>
    rw [FJj_SuccessorModel.zero]
    funext j
    simp only [FJj_SuccessorLiteralStep.state,Nat.zero_le,if_true]
  | succ e ih =>
    rw [FJj_SuccessorModel.succ,FJj_SuccessorLiteralStep.value z e (by omega)]
    exact ih (by omega)

theorem value (z : Fin 10 → K) :
    (FJj_SuccessorModel.eval z 10 (1,z)).2=R0P.SemSource.successorPoint z := by
  have initial : FJj_SuccessorLiteralStep.state z 10=(1,z) := by
    apply Prod.ext
    · rfl
    · funext j
      simp only [FJj_SuccessorLiteralStep.state,if_neg (show ¬10≤j.val by have := j.isLt;omega)]
  rw [←initial]
  exact suffix z 10 (by omega)

theorem reference (z : Fin 10 → K) :
    FJd_LoopReference.successor z=R0P.SemSource.successorPoint z :=
  (FJj_SuccessorOrder.value z).symm.trans (value z)
#print axioms suffix
#print axioms value
#print axioms reference
end AspisR1.FJj_SuccessorLiteral
end
