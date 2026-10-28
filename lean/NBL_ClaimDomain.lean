import NBA_ClaimInputs
import NBL_ViewFields
import LPs_SemanticDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_ClaimDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open LPi_FieldValues

/-- Caller-domain join at the installed claim: the semantic finish, selected
wide-view, compact check/expansion and challenge calls all use the SAME
carriers. No canonical semantic, inactive, gamma, kappa or scratch predicate
is supplied. These facts are derived from their producing executions. -/
theorem source (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (beforeSemantic : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (finish : FinishModel.finish AspisS1ExtractedRoundChildren.children
      {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))}
      D pub pre beforeSemantic challenges obs=ok (.Ok sem))
    (proof semantic compact before y1 : Slice U8)
    (view : AspisR1SelectedWideViewV1.verifier.View)
    (viewCall : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok view))
    (len : compact.val.length=464) (size : before.val.length=928)
    (checked : LPt_External.compact.check_values compact=ok (.Ok ()))
    (expanded : LPt_LPn.Expand.NativeTrace compact.val before.val 29 y1.val)
    (start t1 t2 : transcript.Transcript H) (inactiveBytes : Slice U8)
    (gamma kappa : PE)
    (gc : PreparedModel.scalar NBA_Installed.actual.sampling D start 27#u8 view.y1 true=ok (gamma,t1))
    (kc : PreparedModel.scalar NBA_Installed.actual.sampling D t1 28#u8 inactiveBytes false=ok (kappa,t2)) :
    ∃ (g : Array NE 29#usize) (out : NE),
      FIo_Native.weights.powers 29#usize (NBA_Carriers.back gamma)=ok g ∧
      NBA_Installed.actual.powers 29#usize gamma=ok (mapArray NBA_ClaimCallee.wide g) ∧
      LPq_PreparedTrace.Trace (toClaimSem sem) view.y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        (NBA_Carriers.back (AspisR1SelectedWideViewV1.preparedView view).inactive)
        (NBA_Carriers.back kappa) out ∧ canonE out ∧
      NBA_Installed.actual.claim D sem view.y1 (AspisR1SelectedWideViewV1.preparedView view).inactive
        (mapArray NBA_ClaimCallee.wide g) kappa=ok (.Ok (NBA_ClaimCallee.wide out)) := by
  have hs := LPs_SemanticDomain.source B D pub pre beforeSemantic challenges obs sem finish
  have hi := NBA_WideView.inactive proof semantic y1 view viewCall
  have expansion : LPt_LPn.Expand.NativeTrace compact.val before.val 29 view.y1.val := by
    rw [(NBL_ViewFields.source proof semantic y1 view viewCall).1]
    exact expanded
  exact NBA_ClaimInputs.source D sem hs compact before view.y1 len size checked expansion
    start t1 t2 inactiveBytes gamma (AspisR1SelectedWideViewV1.preparedView view).inactive kappa gc kc hi

#print axioms source
end AspisR1.NBL_ClaimDomain
end
