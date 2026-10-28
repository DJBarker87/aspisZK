import NBL_PrepareTrace
import NBL_ContinuationHash
import NBL_OpeningHashReplay
import NBL_QueryHashReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_PrepareHashTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NBL_BlockTrace PreparedScratchReachability PreparedHashCode
/-- Exact existing cohort preparation code: one chronological trace, full
Prepared value, final scratch and every attempted digest. Native construction
of the local producing executions remains a separate obligation. -/
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
    (digits : List Nat) (last : List UInt32) (rho : aspis_core.field.QM31)
    (division : LPk_Induction.Digits 4 (SamplerBytePass.digits rhoBlock.value) digits last)
    (packed : NBA_Rho.coordinates rho=digits) :
    ∃ (g : Array LPi_FieldValues.NE 29#usize) (claim : LPi_FieldValues.NE),
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
  let C := preparationEffects NBA_Installed.actual NBL_QueryDictionary.boundaries
  have queryRun := NBL_QueryHashReplay.source D opening.alpha1.block.after 31#u8 view.final_message queries
  rw [selected] at queryRun
  have rhoRun := NBL_ScalarHashReplay.rho D {queries.afterAbsorb with state:=state}
    32#u8 emptyPayload rhoBlock digits last rho division packed
  have powerRun : PreparedHashCode.run (C.powers 29#usize opening.output.gamma)=
      ([],ok (mapArray NBA_ClaimCallee.wide g)) := by
    change PreparedHashCode.run (monadLift (NBA_Installed.actual.powers 29#usize opening.gamma.value) : PreparedHashCode.Code _)=_
    rw [NBL_CodeRunLaws.lift_run,powers]
  have claimRun : PreparedHashCode.run (C.claim D sem view.y1
      (AspisR1SelectedWideViewV1.preparedView view).inactive
      (mapArray NBA_ClaimCallee.wide g) opening.output.kappa)=
      ([],ok (.Ok (NBA_ClaimCallee.wide claim))) := by
    change PreparedHashCode.run (monadLift (NBA_Installed.actual.claim D sem view.y1
      (AspisR1SelectedWideViewV1.preparedView view).inactive
      (mapArray NBA_ClaimCallee.wide g) opening.kappa.value) : PreparedHashCode.Code _)=_
    rw [NBL_CodeRunLaws.lift_run,claimed]
  have tail := NBL_ContinuationHash.tail C D sem
    (AspisR1SelectedWideViewV1.preparedView view) old
    (mapArray NBA_ClaimCallee.wide g) opening.output
    (NBL_HashReplay.events D hash (NBL_QueryHashReplay.log queries))
    (NBL_HashReplay.events D hash rhoBlock.log)
    q {queries.afterAbsorb with state:=state} rhoBlock.after 32#u8 rho
    (.Ok (NBA_ClaimCallee.wide claim)) queryRun row rhoRun powerRun claimRun
  have whole := NBL_ContinuationHash.after_opening C D sem
    (AspisR1SelectedWideViewV1.preparedView view) hash old opening.output
    (NBL_HashReplay.events D hash opening.log)
    (NBL_HashReplay.events D hash (NBL_QueryHashReplay.log queries)++
      NBL_HashReplay.events D hash rhoBlock.log) _
    (NBL_OpeningHashReplay.source D sem _ hash opening) tail
  simpa only [NBL_CohortCode.code,NBL_HashReplay.events,List.map_append,List.append_assoc] using whole

#print axioms source
end AspisR1.NBL_PrepareHashTrace
end
