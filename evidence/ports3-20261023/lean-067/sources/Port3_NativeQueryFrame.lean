import Port3_NativeQueryBody

/-! Actual current query/accumulate frames. Release wrapping next advances
because the SAME query's actual array read supplies next<22. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeQueryFrame
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
open Port3_PushFrame (bind_success)

theorem accumulate_fields (ops : Ops) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (node : aspis_core.field.M31)
    (value : aspis_core.field.wide_exact.WideExact) (b bout : verifier.BatchedWeights)
    (bound : a.next.val<256)
    (h : verifier.accumulate_batched_with_node ops p a node value b=ok (out,bout)) :
    out.weights=a.weights ∧ out.next.val=a.next.val+1 := by
  unfold verifier.accumulate_batched_with_node at h
  iterate 10 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  have hp := Result.ok.inj h
  cases hp
  change ok (Usize.wrapping_add a.next 1#usize)=ok next at hn
  have same := Result.ok.inj hn
  refine ⟨rfl,?_⟩
  rw [← same]
  exact Port3_Wrapping.increment a.next bound

theorem query_read_bound (p : verifier.Prepared) (a : verifier.Accumulator)
    (value : U32) (read : Array.index_usize p.queries a.next=ok value) : a.next.val<22 := by
  by_contra bad
  have len : p.queries.val.length=22 := p.queries.property
  have absent : p.queries.val[a.next.val]?=none := List.getElem?_eq_none (by omega)
  simp [Array.index_usize,absent] at read

private theorem guard {T : Type} (b : Bool)
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if b then ok (.Err verifier.Error.Query) else tail) = ok (.Ok out)) :
    tail = ok (.Ok out) := by
  cases b
  · exact h
  · cases h

theorem query_fields (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights)
    (h : verifier.candidate.query_values ops proof p a g obs geometry b=ok (.Ok (out,bout))) :
    a.next.val<22 ∧ out.weights=a.weights ∧ out.next.val=a.next.val+1 := by
  unfold verifier.candidate.query_values at h
  obtain ⟨value,read,h⟩ := bind_success (Array.index_usize p.queries a.next) _ _ h
  have bound := query_read_bound p a value read
  iterate 27 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  have h := guard _ _ _ h
  iterate 11 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
  obtain ⟨pair,accum,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨a1,b1⟩
  obtain ⟨marked,_,h⟩ := bind_success _ _ _ h
  have same := Result.ok.inj h
  cases same
  exact ⟨bound,accumulate_fields ops p a out _ _ b bout (by omega) accum⟩

theorem loop_eq (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b : verifier.BatchedWeights) (end1 : Usize) :
    verifier.candidate.query_loop ops proof p a g obs geometry b end1 =
      AspisR1Stage2.verifier.candidate.query_loop (verifier.candidate.query_values ops)
        proof p a g obs geometry b end1 := rfl

#print axioms accumulate_fields
#print axioms query_read_bound
#print axioms guard
#print axioms query_fields
#print axioms loop_eq
end AspisR1.Port3_NativeQueryFrame
end
