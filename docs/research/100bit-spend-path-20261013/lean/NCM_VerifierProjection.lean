import NCM_Verifier

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_VerifierProjection
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Projection discards only the observer's extra carrier, retaining exact
ordered effects and the Boolean of the existing physical verifier. -/
theorem model_projection (H : Bytes → State) (root : NCE_VerifierCuts.Digest)
    (physical : Slice U8) (s : Carrier) :
    ((eval H (NCM_Verifier.model root physical s)).1,
      (eval H (NCM_Verifier.model root physical s)).2.1) =
        eval H (MultiproofConePhysicalVerify.verify root physical s.scratch) := by
  unfold NCM_Verifier.model MultiproofConePhysicalVerify.verify
  split <;> simp only [eval_bind,annotate_eval,eval,List.append_nil]

/-- All-outcome native-fragment verifier observation, with no successful
verifier, level or row premise. -/
theorem physical {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input = ok (rawOracle H input))
    (node : Node) (row : NCE_Native_Row H node)
    (entry : NCE_VerifierCuts.Entry) (exit : NCE_VerifierCuts.Exit) (finish : NCE_VerifierCuts.Finish)
    (control : NCE_VerifierCuts.NCE_Native_Verifier entry exit finish)
    (pair range : NCE_AdmissionCuts.Predicate) (predicates : NCE_AdmissionCuts.NCE_Native_Admission pair range)
    (root : NCE_VerifierCuts.Digest) (physical : Slice U8) (s : Carrier)
    (size : physical.val.length ≤ 5504) (zero : s.scratch.«at».val = 0) :
    ((eval H (NCM_Verifier.verify node entry exit finish pair range root physical s)).1,
      (eval H (NCM_Verifier.verify node entry exit finish pair range root physical s)).2.1) =
        eval H (MultiproofConePhysicalVerify.verify root physical s.scratch) := by
  rw [NCM_Verifier.association D hash H law node row entry exit finish control pair range predicates root physical s size zero]
  exact model_projection H root physical s

#print axioms model_projection
#print axioms physical
end AspisR1.NCM_VerifierProjection
end
