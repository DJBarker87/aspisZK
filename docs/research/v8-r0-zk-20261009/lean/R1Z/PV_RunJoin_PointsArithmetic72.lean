import R1Z.PV_RunJoin_NativeClaimsApi69
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PointsArithmetic72
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwDictionaryTower.Q

theorem add (a b : Q) : ∃ c,ProverRwDictionaryTower.qAdd a b=ok c := by
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.add (ProverRwDictionaryTower.toQ a) (ProverRwDictionaryTower.toQ b)
  exact ⟨ProverRwDictionaryTower.fromQ c,by simp only [ProverRwDictionaryTower.qAdd,hc,ProverRwDictionaryTower.mapResult]⟩

theorem mul (a b : Q) : ∃ c,ProverRwDictionaryTower.qMul a b=ok c := by
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.mul (ProverRwDictionaryTower.toQ a) (ProverRwDictionaryTower.toQ b)
  exact ⟨ProverRwDictionaryTower.fromQ c,by simp only [ProverRwDictionaryTower.qMul,hc,ProverRwDictionaryTower.mapResult]⟩

theorem sub (a b : Q) : ∃ c,ProverRwDictionaryTower.qSub a b=ok c := by
  obtain ⟨c,hc⟩ := ProverRwP6QuarticTotal.sub (ProverRwDictionaryTower.toQ a) (ProverRwDictionaryTower.toQ b)
  exact ⟨ProverRwDictionaryTower.fromQ c,by simp only [ProverRwDictionaryTower.qSub,hc,ProverRwDictionaryTower.mapResult]⟩

#print axioms add
#print axioms mul
#print axioms sub
end R1Z.PV_RunJoin_PointsArithmetic72
