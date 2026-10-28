import NDO_JGi_CurrentFixture
import NDO_JGi_TX1Dispatch
set_option autoImplicit false
namespace AspisR1.JGi_TX1Ready
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation FirstComposition
open AspisR1ClaimPreparedBridge

/-- Partial SAME-byte readiness. This states complete source returns and the
remaining entry continuation; it does not assert accepted1 or checkpoint identity. -/
theorem inhabited {C H : Type} (ops : Ops) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (input : Array aspis_core.field.wide_exact.WideExact 29#usize) (identified : JGe_TerminalCondition.Identified) :
    let D0 := F3V_OracleDictionary.current JFp_SHADigest.digest D
    let installed := WAdm_Execution.actual ops true query geo JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))
    ∃ (expanded : Slice U8) (pre : AspisR1PublicPreparation.r1_wire.Prefix) (view : verifier.View)
      (sem : r1_semantic.Verified H) (out : verifier.Prepared)
      (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize),
      AspisS1NativeCompact.compact.expand_semantic AspisS1ValuesOwnedInstallation.nativeValues
        JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
      AspisR1PublicPreparation.PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      sourceView JFx_NativeBytes.proof expanded JGe_Payload27.value=ok (.Ok view) ∧
      S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children JGe_Boundaries.value
        D0 (toCurrentPublic JFs_PublicSerialization.value) expanded hash=ok (.Ok sem) ∧
      originalNew (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed D0 sem view hash input=ok (.Ok out,scratch) ∧
      verifier.candidate.tx1 installed D0 (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize hash none=
        JGi_TX1Control.afterScan installed D0 (toCurrentPublic JFs_PublicSerialization.value)
          JFx_NativeBytes.publicInput JFx_NativeBytes.proof hash := by
  dsimp only
  obtain ⟨expanded,pre,view,sem,out,scratch,expand,parse,yexpand,wide,semantic,prepared⟩ :=
    JGi_CurrentFixture.inhabited D hash input identified
  exact ⟨expanded,pre,view,sem,out,scratch,expand,parse,wide,semantic,prepared,
    JGi_TX1Dispatch.writer ops query geo JGe_Boundaries.value (NP6_StdModel.calls (.Ok ())) _ _ _ _⟩
#print axioms inhabited
end AspisR1.JGi_TX1Ready
