import FinishDotIndexedSourceSumV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1FinishDotReaderLawV1
open AspisR1FinishDotDecodedProductTrace
open AspisR1FinishDotReturnedFieldProductV1
open AspisR1FinishDotIndexedSourceSumV1
open AspisR1FinishRelationCurrent AspisR1FinishDotConcreteOps
local notation "Wide" => AspisWideTower.WideExact
local notation "BaseQ" => AspisV8R15.ExactTowerBase.QM31Exact

theorem queryProductWide_eq_mul_embedding (x : FinishE) (q : FinishQM) :
    queryProductWide x q=AspisR1CurrentWide.Proof.decodeFinish x *
      algebraMap BaseQ Wide (finishQMDecoded q) := by
  rw [AspisR1FinishDotReturnedDecodedValueV1.decodeFinish_eq_word_tower]
  apply QuadraticAlgebra.ext <;> simp [queryProductWide,finishQMDecoded]

/-- The arithmetic dot law follows from interpretation of individual source
reads, with every read supplied by the actual successful execution. -/
theorem successful_finish_dot_of_reader_interpretation {W : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM) (out : FinishE)
    (f : Fin 64 → Wide) (weights : Fin 64 → BaseQ)
    (hlen : ws.len.val=64)
    (hfield : ∀ (index : Usize) (value : FinishE) (hi : index.val<64),
      AspisR1CurrentWide.Proof.finishField fm index=ok value →
      AspisR1CurrentWide.Proof.decodeFinish value=f ⟨index.val,hi⟩)
    (hweight : ∀ (index : Usize) (value : FinishQM) (hi : index.val<64),
      Slice.index_usize ws index=ok value → finishQMDecoded value=weights ⟨index.val,hi⟩)
    (hrun : verifier.finish_query_dot
      (withConcreteDot (AspisR1CurrentWide.Proof.finishConcreteField ops)
        AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws=ok (.Ok out)) :
    AspisR1CurrentWide.Proof.decodeFinish out=
      ∑ i : Fin 64,f i * algebraMap BaseQ Wide (weights i) := by
  obtain ⟨n,indices,messages,actualWeights,hn,hreads,hvalue⟩ :=
    successful_finish_indexed_source_sum ops fm ws out hrun
  have hn64 : n=64 := hn.trans hlen
  subst n
  rw [hvalue]
  apply Finset.sum_congr rfl
  intro i hi
  have hr := hreads i
  have hbound : (indices i).val<64 := by rw [hr.1]; exact i.isLt
  have hindex : (⟨(indices i).val,hbound⟩ : Fin 64)=i := Fin.ext hr.1
  rw [queryProductWide_eq_mul_embedding,
    hfield (indices i) (messages i) hbound hr.2.2.1,
    hweight (indices i) (actualWeights i) hbound hr.2.2.2,hindex]

#print axioms queryProductWide_eq_mul_embedding
#print axioms successful_finish_dot_of_reader_interpretation
end AspisR1FinishDotReaderLawV1
