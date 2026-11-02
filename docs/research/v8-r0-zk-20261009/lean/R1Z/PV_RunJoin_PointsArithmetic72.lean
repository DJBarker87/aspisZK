import R1Z.ProverRwSuccessArithmeticTotal
import R1Z.ProverRwP6QuarticTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PointsArithmetic72
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwDictionaryTower.Q

theorem add (a b : Q) : ∃ c,ProverRwDictionaryTower.qAdd a b=ok c := by
  unfold ProverRwDictionaryTower.qAdd
  exact ProverRwSuccessArithmeticTotal.mapped_total _ _ (ProverRwP6QuarticTotal.add _ _)

theorem mul (a b : Q) : ∃ c,ProverRwDictionaryTower.qMul a b=ok c := by
  unfold ProverRwDictionaryTower.qMul
  exact ProverRwSuccessArithmeticTotal.mapped_total _ _ (ProverRwP6QuarticTotal.mul _ _)

theorem sub (a b : Q) : ∃ c,ProverRwDictionaryTower.qSub a b=ok c := by
  unfold ProverRwDictionaryTower.qSub
  exact ProverRwSuccessArithmeticTotal.mapped_total _ _ (ProverRwP6QuarticTotal.sub _ _)

#print axioms add
#print axioms mul
#print axioms sub
end R1Z.PV_RunJoin_PointsArithmetic72
