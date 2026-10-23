import Port3_NativeRowLoop

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeQueryRaw
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
open Port3_PushFrame (bind_success)

theorem accumulate_raw (ops : Ops) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (node : U32) (value : Stage2E)
    (b bout : verifier.BatchedWeights) (weights : a.weights.val.length=64)
    (size : b.raw.val.length=64)
    (h : verifier.accumulate_batched_with_node (Port3_NativeRowFrame.install ops)
      p a node value b=ok (out,bout)) : bout.raw.val.length=64 := by
  unfold verifier.accumulate_batched_with_node at h
  iterate 4 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨mid,rows,h⟩ := bind_success _ _ _ h
  have width : alloc.vec.Vec.len a.weights=64#usize := UScalar.eq_of_val_eq weights
  have rowframe := Port3_NativeRowLoop.fields ops a.weights a.power a.next
    (alloc.vec.Vec.len a.weights) _ 64
    {start:=0#usize,«end»:=alloc.vec.Vec.len a.weights} b mid
    (by rw [width]; decide) (by rw [width,size]; decide) rows
  iterate 6 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  cases Result.ok.inj h
  exact rowframe.1.trans size

private theorem guard {T : Type} (bad : Bool)
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if bad then ok (.Err verifier.Error.Query) else tail)=ok (.Ok out)) :
    tail=ok (.Ok out) := by
  cases bad
  · exact h
  · cases h

theorem query_raw (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (weights : a.weights.val.length=64)
    (size : b.raw.val.length=64)
    (h : verifier.candidate.query_values (Port3_NativeRowFrame.install ops)
      proof p a g obs geometry b=ok (.Ok (out,bout))) :
    out.weights=a.weights ∧ bout.raw.val.length=64 := by
  have frame := Port3_NativeQueryFrame.query_fields (Port3_NativeRowFrame.install ops)
    proof p a out g obs geometry b bout h
  unfold verifier.candidate.query_values at h
  iterate 28 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  have h := guard _ _ _ h
  iterate 11 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨pair,accum,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨a1,b1⟩
  obtain ⟨marked,_,h⟩ := bind_success _ _ _ h
  cases Result.ok.inj h
  exact ⟨frame.2.1,accumulate_raw ops p a out _ _ b bout weights size accum⟩

theorem loop_raw (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (end1 : Usize)
    (weights : a.weights.val.length=64) (size : b.raw.val.length=64)
    (bound : a.next.val≤end1.val)
    (h : verifier.candidate.query_loop (Port3_NativeRowFrame.install ops)
      proof p a g obs geometry b end1=ok (.Ok (out,bout))) :
    out.weights=a.weights ∧ bout.raw.val.length=64 ∧ out.next.val=end1.val := by
  rw [Port3_NativeQueryFrame.loop_eq] at h
  have calls := Port2_QueryLoop.source_calls
    (verifier.candidate.query_values (Port3_NativeRowFrame.install ops))
    proof p g obs geometry end1
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields (Port3_NativeRowFrame.install ops)
      proof p a a1 g obs geometry b b1 h).2.2) a out b bout bound h
  have frame := Port3_QueryRaw.calls_raw _ _ _ _ _ _ _
    (fun a a1 b b1 hw hs h => query_raw ops proof p a a1 g obs geometry b b1 hw hs h)
    weights size calls
  exact ⟨frame.1,frame.2,Port2_QueryLoop.returned_next _ _ _ _ _ _ _ calls⟩

#print axioms accumulate_raw
#print axioms query_raw
#print axioms loop_raw
end AspisR1.Port3_NativeQueryRaw
end
