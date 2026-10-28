import NDO_JGp_PrepareCuts
import NDO_JGp_SemanticIdentity
import NDO_JGp_PreparedQueries
set_option autoImplicit false
namespace AspisR1.JGp_CurrentQueries
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation BorrowedClaimPrepared OriginalSerializerInstallation
open AspisR1ClaimPreparedBridge FirstComposition

theorem source {C H : Type} (base : Ops) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops C) (D : aspis_core.digest.Digest32 H) (hash : H)
    (p : verifier.Prepared) (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (JGp_PrepareLayout.installed base query geo)
      (F3V_OracleDictionary.current JFp_SHADigest.digest D) (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof hash none input=ok (.Ok p,scratch)) :
    p.queries=JFq_Queries.value := by
  obtain ⟨initial,expanded,view,sem,expand,wide,viewsem,verify,newCall⟩ :=
    JGp_PrepareCuts.source base query geo _ hash _ p input scratch success
  have semantic := JGp_SemanticIdentity.source D hash initial expanded sem expand verify
  obtain ⟨other,call,variant,y1,round0,folded,round1,finalMessage,inactive⟩ := JGg_ViewOpening.source expanded
  have same : other=view := core.result.Result.Ok.inj (Result.ok.inj (call.symm.trans wide))
  subst other
  obtain ⟨out,rs,prepared,outEq,scratchEq⟩ := PAln_Borrowed.original_success
    (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed _ sem view hash input scratch p newCall
  have oldVariant : (retainedView view).variant=AspisR1PublicPreparation.transport.Variant.S2 := by
    change retainedVariant view.variant=_
    rw [variant]
    rfl
  have value := JGp_PreparedQueries.source D hash (retainedSem sem) (retainedView view) out
    (mapArray retainedE input) rs semantic.2 oldVariant y1 inactive round0 folded round1 finalMessage prepared
  rw [←outEq]
  exact value
#print axioms source
end AspisR1.JGp_CurrentQueries
