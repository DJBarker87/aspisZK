import R1Z.ProverCommitSourceDecoder
import R1Z.ProverCommitBudgetJoin

/-! Universal coordinate counts for the sequential source model. The source
caller identity/read-log completeness are not inferred from cardinal bounds. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSourceDecoder
attribute [local instance] Classical.propDecidable
open R0Z.MaskLayout R1Z.ProverCommitSourceCarrier

def noiseIndex (c : EligibleCell) : Fin 16 × Fin 1024 :=
  (⟨c.1.1.val, c.2.1⟩, c.1.2)

theorem noiseIndex_injective : Function.Injective noiseIndex := by
  intro a b eq
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun v : Fin 16 × Fin 1024 => v.1.val) eq
  · exact congrArg (fun z : Fin 16 × Fin 1024 => z.2) eq

theorem source_counts : R1Z.CommitReadsR1.RCommitCount L₁ L₂ := by
  have hn := Fintype.card_le_of_injective noiseIndex noiseIndex_injective
  have hr : Fintype.card FreeRow ≤ 1024 := by
    convert Fintype.card_le_of_injective (Subtype.val : FreeRow → Fin 1024) Subtype.val_injective using 1
    simp only [Fintype.card_fin]
  
  simp only [Fintype.card_prod, Fintype.card_fin] at hn
  constructor
  · dsimp only [L₁]
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  · simp only [L₂, Stream2Coord, Fintype.card_prod, Fintype.card_fin]

attribute [local irreducible] L₁ L₂

theorem source_budgets :
    16 * L₁ ≤ E₁ * 8 ∧ 16 * L₂ ≤ E₂ * 8 ∧
    E₁ ≤ 2 * L₁ ∧ E₂ ≤ 2 * L₂ ∧ E₁ ≤ 2^64 ∧ E₂ ≤ 2^64 := by
  have h := R1Z.ProverCommitBudgetJoin.canonical_budgets L₁ L₂ source_counts
  simpa only [E₁, E₂] using And.intro h.1 (And.intro h.2.1 (And.intro (Nat.le_refl (2*L₁)) (And.intro (Nat.le_refl (2*L₂)) h.2.2)))

#print axioms noiseIndex_injective
#print axioms source_counts
#print axioms source_budgets
end R1Z.ProverCommitSourceDecoder
