import NBL_PrepareHashTrace
import NBL_RhoConstruct
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_PrepareAutoRho
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NBL_BlockTrace PreparedScratchReachability PreparedHashCode
/-- The full cohort trace with its rho output and packing trace constructed
from the reached block; no selected rho or division success is a premise. -/
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
    (hash : H) (old : NBL_PrepareControl.Scratch)
    (opening : NBL_OpeningTrace.Trace D sem (AspisR1SelectedWideViewV1.preparedView view) hash)
    (queries : NBL_QueryTrace.Trace D opening.alpha1.block.after 31#u8 view.final_message)
    (q : Array U32 22#usize) (state : NBL_BlockTrace.Bytes32)
    (selected : queries.result=ok (.Ok (q,state)))
    (rhoBlock : Block D {queries.afterAbsorb with state:=state} 32#u8 emptyPayload)
 :
    ∃ (rho : aspis_core.field.QM31) (g : Array LPi_FieldValues.NE 29#usize) (claim : LPi_FieldValues.NE),
      FIo_Native.weights.powers 29#usize (NBA_Carriers.back opening.gamma.value)=ok g ∧
      LPq_PreparedTrace.Trace (toClaimSem sem) view.y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        (NBA_Carriers.back (AspisR1SelectedWideViewV1.preparedView view).inactive)
        (NBA_Carriers.back opening.kappa.value) claim ∧ LPi_FieldValues.canonE claim ∧
      PreparedHashCode.run (NBL_CohortCode.code D sem
        (AspisR1SelectedWideViewV1.preparedView view) hash old)=
        (NBL_HashReplay.events D hash
          (opening.log++NBL_QueryHashReplay.log queries++rhoBlock.log),
        ok (.Ok (output sem (AspisR1SelectedWideViewV1.preparedView view)
          opening.gamma.value opening.kappa.value opening.output.alpha rho q
          (NBA_ClaimCallee.wide claim) rhoBlock.after),mapArray NBA_ClaimCallee.wide g)) := by
  obtain ⟨digits,last,rho,division,packed,native⟩ := NBL_RhoConstruct.source rhoBlock.value
  exact ⟨rho,NBL_PrepareHashTrace.source B D pub pre beforeSemantic challenges obs sem finish
    proof semantic compact before y1 view viewCall len size checked expanded hash old opening queries
    q state selected rhoBlock digits last rho division packed⟩

#print axioms source
end AspisR1.NBL_PrepareAutoRho
end
