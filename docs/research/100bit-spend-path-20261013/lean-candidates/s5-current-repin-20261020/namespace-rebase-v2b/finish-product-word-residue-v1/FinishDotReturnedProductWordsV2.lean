import AspisR1FinishDotReturnedProductWords
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotReturnedProductWordsV2
open AspisR1FinishDotDecodedProductTrace AspisR1FinishRelationCurrent
open AspisR1FinishDotConcreteOps

theorem successful_finish_words_are_reduced_accumulators {W : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM) (out : FinishE)
    (hrun : verifier.finish_query_dot
      (withConcreteDot (AspisR1CurrentWide.Proof.finishConcreteField ops)
        AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws = .ok (.Ok out)) :
    ∃ final : PushState, ∃ xs : List (Usize × FinishE × FinishQM),
      stateDelta final = deltaSum xs ∧
      List.map (fun w => w.val) (AspisR1FinishDotSourceABI.finishWords out) =
        List.map (fun x : U64 => x.val % AspisV8R17.RawReducer.P)
          (final.c0.sums.val ++ final.c1.sums.val) := by
  obtain ⟨final,xs,hfinish,hwords,hdelta,hlen,hseq,hreads⟩ :=
    AspisR1FinishDotReturnedProductWords.successful_current_finish_query_product_words
      ops fm ws out hrun
  refine ⟨final,xs,hdelta,?_⟩
  rw [hwords]
  simp only [List.map_map, Function.comp_def,
    AspisR1EbyKFinish.Proof.word,
    AspisR1CanonicalDotFinish.Proof.canonicalWord_val]

#print axioms successful_finish_words_are_reduced_accumulators
end AspisR1FinishDotReturnedProductWordsV2
