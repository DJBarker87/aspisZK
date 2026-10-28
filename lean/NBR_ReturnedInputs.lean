import NBR_PrepareTotal
import NBR_SemanticFinish
import NBR_BufferJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBR_ReturnedInputs
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisR1ClaimPreparedBridge
open NBL_BlockTrace PreparedScratchReachability PreparedHashCode AspisV8R19.DuplexFrames
/-- SAME proof/allocation producer associations. The finish observation is
DERIVED from the full semantic verifier on the produced semantic bytes.
This does not assert that Rust supplies those model observations. -/
theorem source (B : FinishModel.Boundaries) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof logical semantic y1 : Slice U8)
    (full : proof.val.length=57607) (allocated : logical.val.length=14759)
    (semanticCall : AspisS1NativeCompact.compact.expand_semantic
      AspisS1ValuesOwnedInstallation.nativeValues (NBR_ProducerBuffers.semanticInput proof)
      (NBR_ProducerBuffers.semanticInitial logical)=ok (.Ok (),semantic))
    (y1Call : LPt_External.compact.expand_values (NBR_ProducerBuffers.compactInput proof)
      (NBR_ProducerBuffers.y1Initial logical)=ok (.Ok (),y1))
    (checked : LPt_External.compact.check_values (NBR_ProducerBuffers.compactInput proof)=ok (.Ok ()))
    (view : AspisR1SelectedWideViewV1.verifier.View)
    (viewCall : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok view))
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (sem : r1_semantic.Verified H)
    (verifyCall : VerifyPrefix.verify (FinishModel.finish AspisS1ExtractedRoundChildren.children
      {B with claims:=ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ()))})
      D pub semantic hash obs=ok (.Ok sem))
    (total : NBR_BlockConstruct.Total D) (old : NBL_PrepareControl.Scratch) :
    ∃ finalLogical : Slice U8,
      finalLogical.val=semantic.val++y1.val ∧ finalLogical.val.length=14759 ∧
      NBL_SlicePort.segment finalLogical 0#usize 13831#usize=semantic ∧
      NBL_SlicePort.segment finalLogical 13831#usize 14759#usize=y1 ∧
      ∃ rows : List Bytes,
        PSem_Rows.expandRows 27 0 (MultiproofConeCanonical.bytesOf
          ((NBR_ProducerBuffers.semanticInput proof).val.drop 32))=some rows ∧
        MultiproofConeCanonical.bytesOf (semantic.val.drop 32)=rows.flatten ∧
    ∃ opening : NBL_OpeningTrace.Trace D sem (AspisR1SelectedWideViewV1.preparedView view) hash,
    ∃ queries : NBL_QueryTrace.Trace D opening.alpha1.block.after 31#u8 view.final_message,
      (∃ result,queries.result=ok result) ∧
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
  have semSize : (NBR_ProducerBuffers.semanticInitial logical).val.length=13831 :=
    NBR_RangeGeometry.length logical 0#usize 13831#usize 13831 (by scalar_tac) (by change 13831≤_;omega)
  have compactSize : (NBR_ProducerBuffers.compactInput proof).val.length=464 :=
    NBR_RangeGeometry.length proof 7031#usize 7495#usize 464 (by scalar_tac) (by change 7495≤_;omega)
  have ySize : (NBR_ProducerBuffers.y1Initial logical).val.length=928 :=
    NBR_RangeGeometry.length logical 13831#usize 14759#usize 928 (by scalar_tac) (by change 14759≤_;omega)
  obtain ⟨semLength,rows,rowCall,rowBytes⟩ := NBR_SemanticReturn.returned
    (NBR_ProducerBuffers.semanticInput proof) (NBR_ProducerBuffers.semanticInitial logical)
    semantic semSize semanticCall
  have yLength := (NBR_ExpansionReturn.source (NBR_ProducerBuffers.compactInput proof)
    (NBR_ProducerBuffers.y1Initial logical) y1 compactSize ySize y1Call).2.1
  obtain ⟨pre,initial,before,challenges,parse,start,begin,finish⟩ :=
    NBR_SemanticFinish.source _ D pub semantic hash obs sem verifyCall
  have joined := NBR_BufferJoin.source semantic y1 semLength yLength
  refine ⟨NBR_BufferJoin.logical semantic y1 semLength yLength,rfl,joined.1,
    joined.2.1,joined.2.2,rows,rowCall,rowBytes,?_⟩
  exact NBR_PrepareTotal.source B D pub pre before challenges obs sem finish
    proof semantic (NBR_ProducerBuffers.compactInput proof) (NBR_ProducerBuffers.y1Initial logical)
    y1 view viewCall compactSize ySize checked y1Call full total hash old

#print axioms source
end AspisR1.NBR_ReturnedInputs
end
