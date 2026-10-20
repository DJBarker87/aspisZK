import R1Z.ProverCommitCompletionAdapter
import R1Z.ProverCommitBudgetJoin
import R1Z.FinalR1PBin

/-! Joins to the actual endpoint predicates. Caller/decoder equalities remain
explicit inputs, never replaced by a model-only source instance. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommit5Joins
open R0P R0Z.JointView R0Z.FsStatement R1Z.GamesR1 R1Z.GamesR1PBin
open R1Z.ProverCommitTapeCompletion R1Z.CommitReadsR1 R1Z.FinalR1PBin
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
  {W : R1Wire K CommitHandle Aux} (Pr : R1ProverP K CommitHandle Aux F W)

/-- The endpoint counter slots follow from its count and block slots. -/
theorem counter_slots (L₁ L₂ : Nat) (cells : RCommitCount L₁ L₂)
    (blocks₁ : Pr.E₁ ≤ 2 * L₁) (blocks₂ : Pr.E₂ ≤ 2 * L₂) :
    Pr.E₁ ≤ 2^64 ∧ Pr.E₂ ≤ 2^64 :=
  R1Z.ProverCommitBudgetJoin.counter_bounds Pr.E₁ Pr.E₂ L₁ L₂ cells blocks₁ blocks₂

/-- Completion's failure preservation joins directly to RExh with the actual
wordsE transport. This requires the real caller decoder and failure law. -/
theorem exhaustion_slot
    (decode : ((Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) →
      Option (SourceTape K F))
    (pad : ((Fin Pr.E₁ → OracleAnswer) × (Fin Pr.E₂ → OracleAnswer)) → Padding K F)
    (caller : ∀ e₁ e₂, Pr.tapeOf e₁ e₂ = completeDecode decode ((e₁,e₂), pad (e₁,e₂)))
    (L₁ L₂ : Nat)
    (failure : ∀ e₁ e₂, decode (e₁,e₂) = none →
      Exhausted (wordsE Pr.E₁ e₁) L₁ ∨ Exhausted (wordsE Pr.E₂ e₂) L₂) :
    RExh Pr L₁ L₂ := by
  intro e₁ e₂ bad
  rw [caller] at bad
  exact failure e₁ e₂ ((completion_failure decode _).mp bad)

#print axioms counter_slots
#print axioms exhaustion_slot
end R1Z.ProverCommit5Joins
