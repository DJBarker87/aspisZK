import R1Z.PV_L2_F3SourceArrays
import R1Z.PV_L2_F3Tape
import R1Z.PrivacyR1AcctModel

/-! The actual two caller domains and fixed source budgets, with no capacity
or successful-history assumption passed by the caller. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3SourceBudget
open R1Z.ProverCommitWordCarrier R0Z.FsStatement R1Z.ProverCommitSourceDecoder R1Z.ProverCommitOwnedDecoder
  R1Z.PV_L2_F3SourceArrays
attribute [local irreducible] sourceBase L₁ L₂ E₁ E₂
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]

theorem masking (answers : Fin E₁ → OracleAnswer) :
    sourceArrays (K := K) (blockHash answers)
      AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN L₁ =
        PV_L2_F3Blocks.blocks E₁ L₁ answers :=
  source_arrays answers _ PrivacyR1AcctModel.counter₁ L₁ source_budgets.1

theorem entropy (answers : Fin E₂ → OracleAnswer) :
    sourceArrays (K := K) (blockHash answers)
      AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN L₂ =
        PV_L2_F3Blocks.blocks E₂ L₂ answers :=
  source_arrays answers _ PrivacyR1AcctModel.counter₂ L₂ source_budgets.2.1

def sourcePair (input : Inputs) := do
  let a ← sourceArrays (K := K) (blockHash input.1)
    AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN L₁
  let b ← sourceArrays (K := K) (blockHash input.2)
    AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN L₂
  pure ((a.1,b.1),(a.2,b.2))

theorem source_pair (input : Inputs) :
    sourcePair (K := K) input = PV_L2_F3Pair.pair E₁ E₂ L₁ L₂ input := by
  unfold sourcePair
  rw [masking,entropy]
  rfl

#print axioms source_pair
#print axioms masking
#print axioms entropy
end R1Z.PV_L2_F3SourceBudget
