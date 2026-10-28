import NDO_JGi_CurrentSemantic
import NDO_JGi_OriginalPreparation
set_option autoImplicit false
namespace AspisR1.JGi_CurrentFixture
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge FirstComposition S1SemanticCarrier

theorem inhabited {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) (identified : JGe_TerminalCondition.Identified) :
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix) (view : verifier.View)
      (sem : r1_semantic.Verified H) (out : verifier.Prepared)
      (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize),
      AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
        JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      AspisS1ValuesOwnedInstallation.expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),JGe_Payload27.value) ∧
      sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
        (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
        expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        (F3V_OracleDictionary.current JFp_SHADigest.digest D) sem view hash input=ok (.Ok out,scratch) := by
  obtain ⟨expanded,pre,view,sem,out,scratch,expand,parse,yexpand,wide,finish,prepare⟩ :=
    JGi_PreparationFixture.inhabited D hash (mapArray retainedE input) identified
  have semantic := JGi_CurrentSemantic.source D hash expanded pre sem expand parse finish
  have prepared := JGi_OriginalPreparation.source _ sem view hash input out scratch prepare
  exact ⟨expanded,pre,view,currentSem sem,currentPrepared out,mapArray currentE scratch,
    expand,parse,yexpand,wide,semantic,prepared⟩
#print axioms inhabited
end AspisR1.JGi_CurrentFixture
