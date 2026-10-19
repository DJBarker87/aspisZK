import R0C.SlackStatement
import R0C.ModuloField
import R0C.QuerySampler

/-! A3's concrete probability facts. Field clauses are proved at delta0.
The query clause is proved for the retained PROGRAM's successful outcomes;
it is not misidentified with the total one-block sampler law. -/
set_option autoImplicit false
namespace R0C.ConcreteSlack
open R0C.SlackStatement AspisWideTower AspisCircleGroupOrder
open AspisV8R19.SourceDuplexStep
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
noncomputable section
attribute [local instance] Classical.propDecidable

theorem delta0_nonneg : 0 ≤ delta0 := by norm_num [delta0, P]

theorem ordinary_budget :
    257 / (256^32 : ℚ) = (1+delta0) / (Fintype.card WideExact : ℚ) := by
  rw [wideExact_card]
  norm_num [delta0, P]

theorem gamma_budget :
    257 / (256^32 : ℚ) ≤ (1+delta0) / ((Fintype.card WideExact : ℚ)-1) := by
  rw [wideExact_card]
  norm_num [delta0, P]

theorem gamma_nonzero (s : State) : ModuloField.gamma s ≠ 0 :=
  ModuloField.gamma_ne_zero s

theorem gamma_mass (c : WideExact) :
    mean (fun s => indicator (ModuloField.gamma s = c)) ≤
      (1+delta0) / ((Fintype.card WideExact : ℚ)-1) :=
  (ModuloField.gamma_mass_257 c).trans gamma_budget

/-- This one sampler supplies kappa, tau, and alpha. -/
theorem ordinary_mass (c : WideExact) :
    mean (fun s => indicator (ModuloField.ordinary s = c)) ≤
      (1+delta0) / (Fintype.card WideExact : ℚ) :=
  (ModuloField.ordinary_mass_257 c).trans_eq ordinary_budget

/-- The requested multiplicative query budget is implied by the stronger
successful-query bound, but only at the retained program's type and law. -/
theorem query_success_mass (s : State) (M : Finset (Fin (2^18))) :
    independentMean (QuerySampler.sampler s).toProgram
      (fun v => indicator (QuerySampler.acceptedSubset M v.2.1)) ≤
      (1+delta0) * ((M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ)) := by
  apply (QuerySampler.sampler_subset_le s M).trans
  have hc : (0 : ℚ) ≤ (M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := by positivity
  nlinarith [delta0_nonneg]

#print axioms delta0_nonneg
#print axioms ordinary_budget
#print axioms gamma_budget
#print axioms gamma_nonzero
#print axioms gamma_mass
#print axioms ordinary_mass
#print axioms query_success_mass
end
end R0C.ConcreteSlack
