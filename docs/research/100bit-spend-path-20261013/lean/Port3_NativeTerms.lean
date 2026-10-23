import Port3_NativeQueryRaw

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeTerms
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)

/-- Native row traversal preserves terms, and the actual accumulation then
increments that counter exactly once with the emitted wrapping operation. -/
theorem accumulate_terms (ops : Ops) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (node : U32) (value : Stage2E)
    (b bout : verifier.BatchedWeights) (weights : a.weights.val.length=64)
    (size : b.raw.val.length=64)
    (h : verifier.accumulate_batched_with_node (Port3_NativeRowFrame.install ops)
      p a node value b=ok (out,bout)) :
    bout.terms=Usize.wrapping_add b.terms 1#usize := by
  unfold verifier.accumulate_batched_with_node at h
  iterate 4 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨mid,rows,h⟩ := bind_success _ _ _ h
  have width : alloc.vec.Vec.len a.weights=64#usize := UScalar.eq_of_val_eq weights
  have frame := Port3_NativeRowLoop.fields ops a.weights a.power a.next
    (alloc.vec.Vec.len a.weights) _ 64
    {start:=0#usize,«end»:=alloc.vec.Vec.len a.weights} b mid
    (by rw [width]; decide) (by rw [width,size]; decide) rows
  obtain ⟨terms,ht,h⟩ := bind_success _ _ _ h
  iterate 5 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  cases Result.ok.inj h
  change ok (Usize.wrapping_add mid.terms 1#usize)=ok terms at ht
  have same := Result.ok.inj ht
  change terms=Usize.wrapping_add b.terms 1#usize
  rw [←same,frame.2]

#print axioms accumulate_terms
end AspisR1.Port3_NativeTerms
end
