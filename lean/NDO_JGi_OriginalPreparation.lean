import NDO_JGi_PreparationFixture
import RPz7_S1SemanticCarrierV1
set_option autoImplicit false
namespace AspisR1.JGi_OriginalPreparation
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge

theorem source {H : Type} (D : aspis_core.digest.Digest32 H)
    (sem : AspisR1PublicPreparation.r1_semantic.Verified H) (view : verifier.View) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (out : AspisR1PublicPreparation.verifier.Prepared)
    (scratch : Array AspisR1PublicPreparation.aspis_core.field.WideExact 29#usize)
    (call : AspisR1PublicPreparation.PreparedScratchModel.prepare closedHashBoundaries (retainedDigest D) sem
      (retainedView view) hash (mapArray retainedE input)=ok (.Ok out,scratch)) :
    originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
      D (S1SemanticCarrier.currentSem sem) view hash input=
      ok (.Ok (currentPrepared out),mapArray currentE scratch) := by
  rw [originalNew_eq_transport,S1SemanticCarrier.semantic_round]
  change (do
    let (r,s) ← AspisR1PublicPreparation.PreparedScratchModel.prepare closedHashBoundaries
      (retainedDigest D) sem (retainedView view) hash (mapArray retainedE input)
    ok ((match r with | .Ok x => core.result.Result.Ok (currentPrepared x) | .Err e => core.result.Result.Err (currentError e)),mapArray currentE s))=_
  rw [call,bind_tc_ok]
#print axioms source

theorem inhabited {H : Type} (D : aspis_core.digest.Digest32 H) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) (identified : JGe_TerminalCondition.Identified) :
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix) (view : verifier.View)
      (sem : AspisR1PublicPreparation.r1_semantic.Verified H)
      (out : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize),
      AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
        JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
        (F3V_OracleDictionary.current JFp_SHADigest.digest D) (S1SemanticCarrier.currentSem sem) view hash input=ok (.Ok out,scratch) := by
  obtain ⟨expanded,pre,view,sem,out,scratch,expand,parse,yexpand,wide,finish,prepare⟩ :=
    JGi_PreparationFixture.inhabited D hash (mapArray retainedE input) identified
  exact ⟨expanded,pre,view,sem,currentPrepared out,mapArray currentE scratch,
    expand,parse,wide,source _ _ _ _ _ _ _ prepare⟩
#print axioms inhabited
end AspisR1.JGi_OriginalPreparation
