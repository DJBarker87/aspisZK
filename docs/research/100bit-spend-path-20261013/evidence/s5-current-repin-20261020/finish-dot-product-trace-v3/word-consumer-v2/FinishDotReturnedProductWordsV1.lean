import AspisR1FinishDotDecodedProductTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotReturnedProductWords
open AspisR1FinishDotDecodedProductTrace AspisR1FinishRelationCurrent

/-- The successful source finish exposes exactly the eight reducer words for
its final raw accumulators. The accompanying trace identifies each residue
coordinate with the ordered sum of per-query product coefficients. -/
theorem successful_current_finish_query_product_words {W : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM) (out : FinishE)
    (hrun : verifier.finish_query_dot
      (withConcreteDot (AspisR1CurrentWide.Proof.finishConcreteField ops)
        AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws = .ok (.Ok out)) :
    ∃ final : PushState, ∃ xs : List (Usize × FinishE × FinishQM),
      AspisR1FinishDotSourceABI.finishFromPush final = .ok out ∧
      AspisR1FinishDotSourceABI.finishWords out =
        (final.c0.sums.val ++ final.c1.sums.val).map AspisR1EbyKFinish.Proof.word ∧
      stateDelta final = deltaSum xs ∧ xs.length = ws.len.val ∧
      (∀ k, ∀ hk : k < xs.length, (xs[k]'hk).1.val = k) ∧
      (∀ t ∈ xs, t.1 < ws.len ∧
        AspisR1CurrentWide.Proof.finishField fm t.1 = .ok t.2.1 ∧
        Slice.index_usize ws t.1 = .ok t.2.2) := by
  obtain ⟨final,xs,hfinish,hcount,hdelta,hlen,hseq,hreads⟩ :=
    AspisR1FinishDotDecodedProductTrace.successful_current_finish_query_product_trace
      ops fm ws out hrun
  have hwords := AspisR1FinishDotSourceABI.finishFromPush_success_canonical
    final out hfinish
  exact ⟨final,xs,hfinish,hwords.2,hdelta,hlen,hseq,hreads⟩

#print axioms successful_current_finish_query_product_words
end AspisR1FinishDotReturnedProductWords
