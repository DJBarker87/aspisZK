import NDO_JGi_PrefixCalls
import NDO_JGi_PreparationFixture
set_option autoImplicit false
namespace AspisR1.JGi_SemanticVerify
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge

theorem source {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (expanded : Slice U8) (pre : r1_wire.Prefix) (sem : r1_semantic.Verified H)
    (expand : AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
      JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded))
    (parse : PrefixAdapter.parseAccepted expanded=ok (.Ok pre))
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D))
      JFs_PublicSerialization.value pre (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript H)
      JFm_Begin.challenges none=ok (.Ok sem)) :
    VerifyPrefix.verify (FinishModel.finish AspisS1ExtractedRoundChildren.children JGe_Boundaries.value)
      (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D))
      JFs_PublicSerialization.value expanded hash none=ok (.Ok sem) := by
  obtain ⟨initial,begin⟩ := JGi_PrefixCalls.source D hash expanded pre expand parse
  unfold VerifyPrefix.verify
  simp only [parse,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark,
    initial,begin,Aeneas.Std.uncurry,finish]
#print axioms source
end AspisR1.JGi_SemanticVerify
