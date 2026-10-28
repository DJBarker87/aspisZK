import NDO_JHn_R_JHe_NativeAssociation
import NDO_JHn_R_JHe_ConfigDigest
import NDO_JHn_R_JHe_TransportCall
import NDO_JHn_R_JHe_OriginalCandidate
import NDO_JHn_R_JHe_PreparedInventory
import NDO_JHe_Natives
import NDO_JGx_RealStatement
import NDO_JFs_SourceProjection
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_ChildBridge
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
/-- Installs the SAME candidate return into the actual first_decoded child.
No replacement child observation or independently chosen saved output. -/
theorem source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (saved : alloc.vec.Vec U8)
    (returned : verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved)) :
    AdapterRw.first_decoded (JHe_Natives.sdk base stage)
      (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof 10#usize=ok (.Ok saved) := by
  have original := JHe_OriginalCandidate.source
    (JGp_Allocation.base (Op5T_Concrete.current JGp_Seeds.base)) true
    JHe_PreparedInventory.query JHe_PreparedInventory.geometry JGe_Boundaries.value
    (NP6_StdModel.calls (.Ok ())) digest () (toCurrentPublic JFs_PublicSerialization.value)
    JFx_NativeBytes.publicInput JFx_NativeBytes.proof saved
    JHe_PreparedInventory.owner JHe_PreparedInventory.ports returned
  have call := @JHe_TransportCall.source Unit
    (DrvC_Installation.currentInstalled (JHe_Natives.configuration base stage))
    {installed with op16:=Tx1Q_Install.writer}
    (DrvC_Installation.currentDigest (JHe_Natives.configuration base stage)) digest
    (JHe_NativeAssociation.source (JHe_SdkLeaves.install base) stage)
    (JHe_ConfigDigest.source (JHe_SdkLeaves.install base) stage)
    () (toCurrentPublic JFs_PublicSerialization.value) JFx_NativeBytes.publicInput
    JFx_NativeBytes.proof 10#usize saved original
  have semantic : AspisS6CurrentVerifierCarrier.toPublic (S6N_Getters.publicValue JGx_RealStatement.value)=
      toCurrentPublic JFs_PublicSerialization.value := by rfl
  unfold AdapterRw.first_decoded
  rw [show AdapterRw.observer (JHe_Natives.sdk base stage)=ok none from rfl,bind_tc_ok]
  change (do
    let result ← AspisS6CurrentFirstInstallation.current
      (DrvC_Installation.currentInstalled (JHe_Natives.configuration base stage))
      (DrvC_Installation.digest (JHe_Natives.configuration base stage))
      (S6N_Getters.publicValue JGx_RealStatement.value) JFx_NativeBytes.publicInput
      JFx_NativeBytes.proof 10#usize () none
    AdapterRw.core.result.Result.map_err _ result _)=_
  dsimp only [DrvC_Installation.currentDigest] at call
  unfold AspisS6CurrentFirstInstallation.current
  rw [AspisS6CurrentFirstInstallation.observer_none,semantic,call]
  rfl
#print axioms source
end AspisR1.JHh_ChildBridge
end
