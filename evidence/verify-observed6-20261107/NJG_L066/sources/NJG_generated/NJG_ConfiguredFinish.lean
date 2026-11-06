import NJG_FinishInstall
set_option autoImplicit false
namespace AspisR1.NJG_ConfiguredFinish
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem unwrap : (core.result.Result.unwrap core.fmt.DebugTryFromSliceError)=S1SemanticRootCopy.unwrapRoot := by
 funext reply
 cases reply <;> rfl

/-- The deployed FIp installer already fixes the ordered from_fn model. Its
root-copy installer fixes the same complete unwrap, including panic failure.
No unrestricted callback/dictionary premise is added. -/
theorem model (seed : FinishModel.Boundaries) :
 NJG_FinishInstall.model (S1SemanticRootCopy.install (FIp_Install.boundaries seed))=
 S1SemanticRootCopy.install (FIp_Install.boundaries seed) := by
 unfold NJG_FinishInstall.model S1SemanticRootCopy.install FIp_Install.boundaries
 rw [unwrap]
 rfl

theorem source {H : Type} (R : RoundModel.Boundaries) (seed : FinishModel.Boundaries)
 (D : aspis_core.Digest32 H) (pubdata : pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pre : r1_wire.Prefix) (t : r1_wire.SemanticTranscript H) (c : r1_wire.Challenges) :
 NJG_FinishBody.r1_semantic.verify_finish
  (NJG_FinishInstall.install R (S1SemanticRootCopy.install (FIp_Install.boundaries seed))) D pubdata pre t c none=
 FinishModel.finish R (S1SemanticRootCopy.install (FIp_Install.boundaries seed)) D pubdata pre t c none := by
 rw [NJG_FinishInstall.source,model]

#print axioms unwrap
#print axioms model
#print axioms source
end AspisR1.NJG_ConfiguredFinish
