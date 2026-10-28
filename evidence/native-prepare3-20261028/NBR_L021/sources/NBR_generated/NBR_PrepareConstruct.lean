import NBR_OpeningConstruct
import NBR_QueryConstruct
import NBR_ExpansionReturn
import NBL_PrepareAutoRho
import NBL_PrepareHashReject
import NBL_ViewDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBR_PrepareConstruct
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NBL_BlockTrace PreparedScratchReachability PreparedHashCode
/-- Construct ONE linked opening/query carrier from producer returns. Every
query rejection and successful suffix below belongs to that SAME carrier.
This is the existing cohort code; native prefix/semantic association is not
asserted by replacing its producer observations with this theorem. -/
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
    (expanded : LPt_External.compact.expand_values compact before=ok (.Ok (),y1))
    (full : proof.val.length=57607)
    (total : NBR_BlockConstruct.Total D)
    (hash : H) (old : NBL_PrepareControl.Scratch)
 :
    ∃ opening : NBL_OpeningTrace.Trace D sem (AspisR1SelectedWideViewV1.preparedView view) hash,
    ∃ queries : NBL_QueryTrace.Trace D opening.alpha1.block.after 31#u8 view.final_message,
      (∀ error, queries.result=ok (.Err error) →
        run (NBL_CohortCode.code D sem (AspisR1SelectedWideViewV1.preparedView view) hash old)=
          (NBL_HashReplay.events D hash (opening.log++NBL_QueryHashReplay.log queries),
            ok (.Err .Transcript,old))) ∧
      (∀ (q : Array U32 22#usize) (state : NBL_BlockTrace.Bytes32), queries.result=ok (.Ok (q,state)) →
        ∃ rhoBlock : Block D {queries.afterAbsorb with state:=state} 32#u8 emptyPayload,
        ∃ (rho : aspis_core.field.QM31) (g : Array LPi_FieldValues.NE 29#usize) (claim : LPi_FieldValues.NE),
          FIo_Native.weights.powers 29#usize (NBA_Carriers.back opening.gamma.value)=ok g ∧
          LPq_PreparedTrace.Trace (toClaimSem sem) view.y1 (XRo_Join_Carriers.arr LPq_Powers.claim g)
            (NBA_Carriers.back (AspisR1SelectedWideViewV1.preparedView view).inactive)
            (NBA_Carriers.back opening.kappa.value) claim ∧ LPi_FieldValues.canonE claim ∧
          run (NBL_CohortCode.code D sem (AspisR1SelectedWideViewV1.preparedView view) hash old)=
            (NBL_HashReplay.events D hash (opening.log++NBL_QueryHashReplay.log queries++rhoBlock.log),
              ok (.Ok (output sem (AspisR1SelectedWideViewV1.preparedView view)
                opening.gamma.value opening.kappa.value opening.output.alpha rho q
                (NBA_ClaimCallee.wide claim) rhoBlock.after),mapArray NBA_ClaimCallee.wide g))) := by
  obtain ⟨_,_,variant,_,roundSize,_,root,rootCall,_⟩ :=
    NBL_ViewDomains.source proof semantic y1 full view viewCall
  have preparedVariant : (AspisR1SelectedWideViewV1.preparedView view).variant=.S2 := by
    change (match view.variant with | .S1=>_ | .S2=>_ | .D=>_)=_
    rw [variant]
  obtain ⟨opening⟩ := NBR_OpeningConstruct.source D total sem
    (AspisR1SelectedWideViewV1.preparedView view) hash preparedVariant root rootCall roundSize
  obtain ⟨queries⟩ := NBR_QueryConstruct.source D total opening.alpha1.block.after
    31#u8 view.final_message (by decide)
  refine ⟨opening,queries,?_,?_⟩
  · intro error rejected
    exact NBL_PrepareHashReject.source D sem _ hash old opening queries error rejected
  · intro q state selected
    obtain ⟨rhoBlock⟩ := NBR_BlockConstruct.block D total
      {queries.afterAbsorb with state:=state} 32#u8 emptyPayload (by decide)
    exact ⟨rhoBlock,NBL_PrepareAutoRho.source B D pub pre beforeSemantic challenges obs sem finish
      proof semantic compact before y1 view viewCall len size checked
      (NBR_ExpansionReturn.source compact before y1 len size expanded).1
      hash old opening queries q state selected rhoBlock⟩

#print axioms source
end AspisR1.NBR_PrepareConstruct
end
