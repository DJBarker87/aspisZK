import R1Z.ProverCommitOwnedArrayLaw
import R1Z.ProverCommitCallerInstance
import R1Z.PrivacyR1AcctModel
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnedDecoder
open R0Z.FsStatement R0Z.JointView
open R1Z.ProverCommitSourceDecoder R1Z.ProverCommitTapeCompletion
open R1Z.ProverCommitSequentialFibres
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
attribute [local irreducible] E₁ E₂ L₁ L₂ arrayCarrierEquiv

/-- The full fixed operational raw producer, including early rejection and
finite allocation failure, refines the two sequential array decoders. -/
theorem rawArrays_model (a : Fin E₁ → OracleAnswer) (b : Fin E₂ → OracleAnswer) :
    rawArrays (K := K) (blockHash a) (blockHash b) =
      pairDecode (R1Z.ProverCommitWordCarrier.accepted (K := K))
        (E₁*8) (E₂*8) L₁ L₂ (inputEquiv (a,b)) := by
  have first := samples_array (K := K) a
    AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN
    R1Z.PrivacyR1AcctModel.counter₁ L₁ source_budgets.1
  have second := samples_array (K := K) b
    AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN
    R1Z.PrivacyR1AcctModel.counter₂ L₂ source_budgets.2.1
  unfold rawArrays pairDecode
  change _ = (do
    let x ← arrayDecode (R1Z.ProverCommitWordCarrier.accepted (K := K)) (E₁*8) L₁ 16 (R1Z.FinalR1PBin.wordsE E₁ a)
    let y ← arrayDecode (R1Z.ProverCommitWordCarrier.accepted (K := K)) (E₂*8) L₂ 16 (R1Z.FinalR1PBin.wordsE E₂ b)
    pure (x,y))
  rw [← first, ← second]
  cases h₁ : samples (blockHash a) AspisR1ProverStreams.state_only_hiding.MASK_EXPAND_DOMAIN L₁ <;>
    cases h₂ : samples (blockHash b) AspisR1ProverStreams.state_only_entropy.PROFILE21_SOURCE_EXPAND_DOMAIN L₂ <;> rfl

/-- CallerLaw's exact quotient equation for the fixed operational decoder. -/
theorem quotient_decoder (e : Inputs) :
    quotientDecode (fun e : Inputs => decoder (K := K) e.1 e.2) e = quotientDecoder e := by
  change (decodeWith (K := K) (blockHash e.1) (blockHash e.2)).map project = _
  rw [quotient_decodeWith, rawArrays_model]
  rfl

#print axioms rawArrays_model
#print axioms quotient_decoder
end R1Z.ProverCommitOwnedDecoder
