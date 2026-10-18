import ExtractedActualFull25
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.FirstPaired

/-- One actual first success supplies the same semantic and Prepared values to
both the complete semantic finish and actual preparation calls. -/
theorem first_paired {E : Type} (invalidAccountData : E)
    (T : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 Unit)
    (mark : FirstCaller.Phase → Result Unit) (error : verifier.Error → Result E)
    (asf8 proof : Slice U8) (k : Usize) (out : alloc.vec.Vec U8)
    (h : FirstCaller.first invalidAccountData
      (FirstHelperBinding.tx1 T P (FinishModel.finish R B) D) mark error asf8 proof k =
        ok (.Ok out)) :
    ∃ s supplied view sem prepared pre initial afterBegin challenges,
      AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_statement_v1
        asf8 = ok (.Ok s) ∧ supplied = PreparationBinding.preparationPublic s ∧
      T.view proof = ok (.Ok view) ∧
      PrefixAdapter.parseAccepted view.semantic = ok (.Ok pre) ∧
      r1_semantic.public_transcript D supplied () pre.c1_root = ok (.Ok initial) ∧
      r1_wire.begin D pre initial = ok (.Ok challenges,afterBegin) ∧
      FinishModel.finish R B D supplied pre afterBegin challenges
        (some (fun phase => mark (FirstHelperBinding.phaseToFirst phase))) = ok (.Ok sem) ∧
      PreparedModel.prepare P D sem view () = ok (.Ok prepared) := by
  obtain ⟨s,supplied,hd,heq,ht⟩ := FirstCaller.first_success invalidAccountData
    (FirstHelperBinding.tx1 T P (FinishModel.finish R B) D) mark error asf8 proof k out h
  change Tx1Model.tx1 { T with verify := VerifyPrefix.verify (FinishModel.finish R B) } P D
    supplied asf8 proof k () (some (fun phase => mark (FirstHelperBinding.phaseToFirst phase))) =
      ok (.Ok out) at ht
  obtain ⟨_,view,sem,prepared,acc,g,hv,_,hs,_,hp,_,_,_,_⟩ := Tx1Reachability.tx1_success
    { T with verify := VerifyPrefix.verify (FinishModel.finish R B) } P D supplied asf8 proof k ()
    (some (fun phase => mark (FirstHelperBinding.phaseToFirst phase))) out ht
  obtain ⟨pre,initial,afterBegin,challenges,hparse,hh,hb,hf⟩ := VerifyPrefix.verify_success
    (FinishModel.finish R B) D supplied view.semantic ()
    (some (fun phase => mark (FirstHelperBinding.phaseToFirst phase))) sem hs
  exact ⟨s,supplied,view,sem,prepared,pre,initial,afterBegin,challenges,
    hd,heq,hv,hparse,hh,hb,hf,hp⟩

#print axioms first_paired
end AspisR1PublicPreparation.FirstPaired
