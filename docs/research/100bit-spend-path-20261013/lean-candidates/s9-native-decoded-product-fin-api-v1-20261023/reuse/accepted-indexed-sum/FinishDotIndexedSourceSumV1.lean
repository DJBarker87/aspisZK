import AspisR1FinishDotReturnedFieldProductTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1FinishDotIndexedSourceSumV1
open AspisR1FinishDotDecodedProductTrace
open AspisR1FinishDotReturnedFieldProductV1
open AspisR1FinishDotReturnedFieldProductTraceV1
open AspisR1FinishRelationCurrent AspisR1FinishDotConcreteOps

def termProduct (t : Usize × FinishE × FinishQM) : AspisWideTower.WideExact :=
  queryProductWide t.2.1 t.2.2

theorem productSum_eq_map_sum (xs : List (Usize × FinishE × FinishQM)) :
    productSum xs=(xs.map termProduct).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [productSum,List.map_cons,List.sum_cons,termProduct,ih]

theorem productSum_eq_indexed_sum (xs : List (Usize × FinishE × FinishQM)) :
    productSum xs=∑ i : Fin xs.length,termProduct (xs.get i) := by
  rw [productSum_eq_map_sum,←List.ofFn_getElem_eq_map xs termProduct,List.sum_ofFn]
  rfl

/-- The indexed dot-product witnesses are derived from the SAME successful
source execution; every read retains its actual ascending source index. -/
theorem successful_finish_indexed_source_sum {W : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM) (out : FinishE)
    (hrun : verifier.finish_query_dot
      (withConcreteDot (AspisR1CurrentWide.Proof.finishConcreteField ops)
        AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws=ok (.Ok out)) :
    ∃ (n : Nat) (indices : Fin n → Usize) (messages : Fin n → FinishE)
      (weights : Fin n → FinishQM),
      n=ws.len.val ∧
      (∀ i : Fin n,(indices i).val=i.val ∧
        indices i<ws.len ∧
        AspisR1CurrentWide.Proof.finishField fm (indices i)=ok (messages i) ∧
        Slice.index_usize ws (indices i)=ok (weights i)) ∧
      AspisR1CurrentWide.Proof.decodeFinish out=
        ∑ i : Fin n,queryProductWide (messages i) (weights i) := by
  obtain ⟨xs,hlen,hseq,hreads,hvalue⟩ :=
    successful_finish_ordered_field_product_trace ops fm ws out hrun
  refine ⟨xs.length,(fun i => (xs.get i).1),(fun i => (xs.get i).2.1),
    (fun i => (xs.get i).2.2),hlen,?_,?_⟩
  · intro i
    have hm : xs.get i∈xs := List.get_mem xs i
    have hr := hreads (xs.get i) hm
    exact ⟨hseq i.val i.isLt,hr⟩
  · exact hvalue.trans (productSum_eq_indexed_sum xs)

#print axioms productSum_eq_map_sum
#print axioms productSum_eq_indexed_sum
#print axioms successful_finish_indexed_source_sum
end AspisR1FinishDotIndexedSourceSumV1
