import NDO_JGi_SemanticVerify
import RPz7_S1SemanticInstallationV1
set_option autoImplicit false
namespace AspisR1.JGi_CurrentSemantic
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation FirstComposition S1SemanticCarrier
open AspisV8R19.SqueezeOracleBridge

theorem source {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre))
    (finish : AspisR1PublicPreparation.FinishModel.finish AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
      (retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)) JFs_PublicSerialization.value pre
      (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      JFm_Begin.challenges none=ok (.Ok sem)) :
    S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
      expanded hash=ok (.Ok (currentSem sem)) := by
  unfold S1SemanticInstallation.verify
  rw [retained_current_roundtrip]
  have installed : AspisR1PublicPreparation.S1SemanticRootCopy.install JGe_Boundaries.value=JGe_Boundaries.value := rfl
  rw [installed,JGi_SemanticVerify.source D hash expanded pre sem expand parse finish,bind_tc_ok]
#print axioms source
end AspisR1.JGi_CurrentSemantic
