import R1Z.PV_L2_F3SourceBudget
import R1Z.PV_L2_F3Absorption

/-! Join the actual source-shaped caller counts to the law used for absorption.
This does not identify native traces or failed scalar prefixes with this Option. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3SourceJoint
open R1Z.ProverCommitSourceDecoder R1Z.ProverCommitWordCarrier
  R1Z.PV_L2_F3SourceBudget R1Z.PV_L2_F3Tape
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
attribute [local irreducible] sourceBase L₁ L₂ E₁ E₂

def sourceObserved (input : Inputs) :=
  (sourcePair (K := K) input).map (outputEquiv (K := K))

theorem source_observed (input : Inputs) :
    sourceObserved (K := K) input = observed (K := K) input := by
  unfold sourceObserved
  rw [source_pair]
  rfl

theorem source_owned (input : Inputs) :
    (sourceObserved (K := K) input).map Prod.fst =
      (ProverCommitOwnedDecoder.decoder (K := K) input.1 input.2).map
        ProverCommitTapeCompletion.project := by
  rw [source_observed,owned_erases]

#print axioms source_observed
#print axioms source_owned
end R1Z.PV_L2_F3SourceJoint
