import NBL_OpeningTrace
import NBL_QueryTrace
import NBL_ClaimDomain
import NBL_PrepareResults
import NBA_RhoScalar
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_PrepareTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NBL_BlockTrace PreparedScratchReachability

/-- Complete query rejection on the SAME opening/query carriers. No rho,
powers or claim observation and no successful suffix is fabricated. -/
theorem query_error {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (old : NBL_PrepareControl.Scratch) (opening : NBL_OpeningTrace.Trace D sem v hash)
    (queries : NBL_QueryTrace.Trace D opening.alpha1.block.after 31#u8 v.final_message)
    (error : AspisR1Query31Transcript.aspis_core.transcript.QuerySampleError)
    (rejected : queries.result=ok (.Err error)) :
    PreparedScratchModel.prepare NBA_Installed.actual D sem v hash old=ok (.Err .Transcript,old) := by
  have call := NBL_QueryTrace.source D opening.alpha1.block.after 31#u8 v.final_message queries
  rw [rejected] at call
  exact NBL_PrepareResults.prepare_query_error NBA_Installed.actual D sem v hash old opening.output
    .Transcript queries.afterAbsorb (NBL_OpeningTrace.source D sem v hash opening) call

/-- All successful tail fields, powers and claim are constructed on ONE
opening/query/rho trace. Caller-domain facts come from the SAME producers.
This does not assert construction of these observations by Rust. -/
theorem success (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
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
    (digits : List Nat) (last : List UInt32) (rho : aspis_core.field.QM31)
    (division : LPk_Induction.Digits 4 (SamplerBytePass.digits rhoBlock.value) digits last)
    (packed : NBA_Rho.coordinates rho=digits) :
    ∃ (g : Array LPi_FieldValues.NE 29#usize) (claim : LPi_FieldValues.NE),
      FIo_Native.weights.powers 29#usize (NBA_Carriers.back opening.gamma.value)=ok g ∧
      LPq_PreparedTrace.Trace (toClaimSem sem) view.y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
        (NBA_Carriers.back (AspisR1SelectedWideViewV1.preparedView view).inactive)
        (NBA_Carriers.back opening.kappa.value) claim ∧ LPi_FieldValues.canonE claim ∧
      PreparedScratchModel.prepare NBA_Installed.actual D sem
        (AspisR1SelectedWideViewV1.preparedView view) hash old=
        ok (.Ok (output sem (AspisR1SelectedWideViewV1.preparedView view)
          opening.gamma.value opening.kappa.value opening.output.alpha rho q
          (NBA_ClaimCallee.wide claim) rhoBlock.after),mapArray NBA_ClaimCallee.wide g) := by
  have gc := scalar_result D _ _ _ _ opening.gamma
  have kc := scalar_result D _ _ _ _ opening.kappa
  obtain ⟨g,claim,native,powers,trace,canonical,claimed⟩ :=
    NBL_ClaimDomain.source B D pub pre beforeSemantic challenges obs sem finish
      proof semantic compact before y1 view viewCall len size checked expanded
      (⟨opening.seed,hash⟩ : transcript.Transcript H) opening.gamma.block.after opening.kappa.block.after
      (Array.to_slice opening.inactiveBytes) opening.gamma.value opening.kappa.value gc kc
  have qc := NBL_QueryTrace.source D opening.alpha1.block.after 31#u8 view.final_message queries
  rw [selected] at qc
  have rc := NBA_RhoScalar.source D {queries.afterAbsorb with state:=state} rhoBlock.after
    32#u8 emptyPayload rhoBlock.value digits last rho
    (block_result D _ _ _ rhoBlock) division packed
  have row : (31#u8+1#u8 : Result U8)=ok 32#u8 := by
    obtain ⟨x,call,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=31#u8) (y:=1#u8) (by scalar_tac))
    have same : x=32#u8 := by scalar_tac
    simpa only [same] using call
  refine ⟨g,claim,native,trace,canonical,?_⟩
  apply NBL_PrepareResults.after_opening NBA_Installed.actual D sem
    (AspisR1SelectedWideViewV1.preparedView view) hash old opening.output _
    (NBL_OpeningTrace.source D sem _ hash opening)
  exact NBL_PrepareResults.success NBA_Installed.actual D sem
    (AspisR1SelectedWideViewV1.preparedView view) old (mapArray NBA_ClaimCallee.wide g) opening.output
    q {queries.afterAbsorb with state:=state} rhoBlock.after 32#u8 rho (NBA_ClaimCallee.wide claim)
    qc row rc powers claimed

#print axioms query_error
#print axioms success
end AspisR1.NBL_PrepareTrace
end
