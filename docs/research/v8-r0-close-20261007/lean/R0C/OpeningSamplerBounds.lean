import R0C.ModuloField
import R0C.QuerySampler
import R0FS.Hypotheses

/-! Sampler bounds on the existing R0 opening bad sets. The original epsilon,
state function and D2 are untouched. These are concrete distribution facts
for a future interface repair, not an instance of the refuted SamplerLawsD. -/
set_option autoImplicit false
namespace R0C.OpeningSamplerBounds
open AspisWideTower AspisCircleGroupOrder
open AspisR0.Opening AspisR0.ListsResponses AspisR0.Fold
open AspisV8R19.SourceDuplexStep
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
open R0FS
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Close Lambda LambdaR

private theorem card_scale (S : Finset WideExact) (k : Nat) (hk : S.card ≤ k) :
    (S.card : ℚ) * (257 / (256^32 : ℚ)) ≤ k * (257 / (256^32 : ℚ)) := by
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast hk

variable {Sfield : Fin 29 → Subfield WideExact}
  (x : Stmt WideExact Sfield) (y : Fin 29 → Fin 2 → WideExact)

theorem gamma_bad_density :
    mean (fun s => indicator (ModuloField.gamma s ∈ bad0 x y)) ≤
      (336869026605739+16800 : ℚ) * (257 / (256^32 : ℚ)) := by
  have hc : (bad0 x y).card ≤ 336869026605739+16800 := by
    exact (grouped_cardinalities (data x y) 0 0 0 0 0 (by simp)).1
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (ModuloField.gamma_event _).trans (card_scale _ _ hc)

theorem kappa_bad_density (γ v : WideExact) :
    mean (fun s => indicator (ModuloField.ordinary s ∈ bad1 x y γ v)) ≤
      400 * (257 / (256^32 : ℚ)) := by
  exact (ModuloField.ordinary_event _).trans
    (card_scale _ 400 (B4_card (data x y) γ v))

theorem tau_bad_density (γ v κ : WideExact) :
    mean (fun s => indicator (ModuloField.ordinary s ∈ bad2 x y γ v κ)) ≤
      200 * (257 / (256^32 : ℚ)) := by
  exact (ModuloField.ordinary_event _).trans
    (card_scale _ 200 (B5_card (data x y) γ v κ))

theorem alpha_bad_density (γ κ τ : WideExact) (Q : Polynomial WideExact) :
    mean (fun s => indicator (ModuloField.ordinary s ∈ bad3 x y γ κ τ Q)) ≤
      (9396508281246+600 : ℚ) * (257 / (256^32 : ℚ)) := by
  have hc : (bad3 x y γ κ τ Q).card ≤ 9396508281246+600 := by
    unfold bad3
    split
    · exact (grouped_cardinalities (data x y) γ 0 κ τ Q (by assumption)).2.2.2
    · rw [Finset.union_empty]
      have := B6_card (channels (batch (data x y) γ))
      omega
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    (ModuloField.ordinary_event _).trans (card_scale _ _ hc)

omit x y in
/-- The repaired query source retains the original query-row budget. -/
theorem query_budget (s : State) (M : Finset (Fin (2^18))) (hM : M.card ≤ 9557) :
    independentMean (QuerySampler.sampler s).toProgram
      (fun v => indicator (QuerySampler.acceptedSubset M v.2.1)) ≤ ε WideExact 4 := by
  apply (QuerySampler.sampler_subset_le s M).trans
  change (M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ) ≤
    (Nat.choose 9557 22 : ℚ) / (Nat.choose 262144 22 : ℚ)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.choose_le_choose 22 hM

#print axioms gamma_bad_density
#print axioms kappa_bad_density
#print axioms tau_bad_density
#print axioms alpha_bad_density
#print axioms query_budget
end
end R0C.OpeningSamplerBounds
