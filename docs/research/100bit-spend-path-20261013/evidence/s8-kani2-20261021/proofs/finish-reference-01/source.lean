import S8Kani2FinishCertificate
import S8OwnedP6R14Backend

set_option autoImplicit false
noncomputable section
namespace S8Kani2FinishReferenceJoin
open Aeneas Aeneas.Std Result
open S8OwnedP6ValueModel S8OwnedP6Finish
open S8Kani2MutableValue
open AspisR1BatchedWeightsFinishExtraction.batched_weights

def toFinish (q : Q) : F.Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

def toSlice (old : Weights) : FinishSlice :=
  ⟨old.val.map toFinish,by simpa using old.property⟩

/-- At an arbitrary successful raw-row read, the retained mutable value and
new extracted reference value are equal after the literal type transport. -/
theorem value_reference (self : F.BW) (i : Usize) (row : Row)
    (hread : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
      self.raw i=.ok row) :
    F.value self i=.ok (toFinish (modelValue row)) := by
  obtain ⟨x0,x1,x2,x3,m0,m1,m2,m3,h0,h1,h2,h3,r0,r1,r2,r3,hout,_⟩ :=
    AspisR1BatchedWeightsValueActualV19.value_entry_of_vec_success_canonical
      self.raw self.terms i row hread
  have fresh : S8OwnedP6.value_owned row=
      .ok (⟨⟨m0,m1⟩,⟨m2,m3⟩⟩ : Q) := by
    simp only [S8OwnedP6.value_owned,h0,h1,h2,h3,
      S8OwnedP6R14Backend.reducer_repin,r0,r1,r2,r3,bind_tc_ok]
  have hv : modelValue row=(⟨⟨m0,m1⟩,⟨m2,m3⟩⟩ : Q) :=
    Result.ok.inj ((modelValue_success row).symm.trans fresh)
  rw [value_eq_entry,hout,hv]
  rfl

/-- Complete mutable back-write traversal agrees pointwise with the complete
emitted owned reference, for arbitrary destination/raw lengths and U64 rows.
The Rust-to-model P6 step receipts are external evidence, not axioms here. -/
theorem finish_reference_simulation (raw : Raw) (old : Weights) (terms : Usize)
    (hlen : old.length≤raw.length) :
    ∃ referenceOut : Weights, ∃ sourceOut : FinishSlice,
      S8OwnedP6.finish_owned raw old=.ok referenceOut ∧
      referenceOut.length=old.length ∧
      BatchedWeights.finish (⟨raw,terms⟩ : F.BW) (toSlice old)=.ok sourceOut ∧
      ∀ i : Usize, i.val<old.length → ∃ row : Row,
        raw.val[i.val]?=some row ∧
        referenceOut.val[i.val]?=some (modelValue row) ∧
        Slice.index_usize sourceOut i=.ok (toFinish (modelValue row)) := by
  obtain ⟨refOut,href,hrefLen,hrefCells⟩ := finish_total_model raw old hlen
  obtain ⟨sourceOut,hsource,_,hcells⟩ :=
    S8Kani2FinishCertificate.mutable_finish_total (⟨raw,terms⟩ : F.BW) (toSlice old)
      (by simpa [toSlice] using hlen)
  refine ⟨refOut,sourceOut,href,hrefLen,hsource,?_⟩
  intro i hi
  have hr : i.val<raw.length := by omega
  obtain ⟨row,hread,hrow⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec raw i hr)
  have hread' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
      raw i=.ok row := by
    rw [alloc.vec.Vec.index_slice_index]; exact hread
  have hrow' : raw.val[i.val]?=some row := by
    rw [List.getElem?_eq_getElem hr,hrow]
  have hv := value_reference (⟨raw,terms⟩ : F.BW) i row hread'
  have hc := hcells i (by simpa [toSlice,Slice.len] using hi)
  have heq : valueAt (⟨raw,terms⟩ : F.BW) i.val=toFinish (modelValue row) :=
    Result.ok.inj (hc.2.symm.trans hv)
  refine ⟨row,hrow',?_,?_⟩
  · simpa only [hrow',Option.map_some] using hrefCells i.val hi
  · simpa only [heq] using hc.1

#print axioms value_reference
#print axioms finish_reference_simulation
end S8Kani2FinishReferenceJoin
