import Port3_NativeTerms

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeQueryTerms
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)

private theorem guard {T : Type} (bad : Bool)
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if bad then ok (.Err verifier.Error.Query) else tail)=ok (.Ok out)) :
    tail=ok (.Ok out) := by
  cases bad
  · exact h
  · cases h

theorem query_terms (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (weights : a.weights.val.length=64)
    (size : b.raw.val.length=64) (sync : b.terms=a.next)
    (h : verifier.candidate.query_values (Port3_NativeRowFrame.install ops)
      proof p a g obs geometry b=ok (.Ok (out,bout))) : bout.terms=out.next := by
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
  have terms := Port3_NativeTerms.accumulate_terms ops p a out _ _ b bout weights size accum
  apply UScalar.eq_of_val_eq
  rw [terms,sync,Port3_Wrapping.increment a.next (by omega)]
  exact frame.2.2.symm

theorem calls_terms (call : Port2_QueryLoop.LocalCall) (end1 : Nat)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights) (n : Nat)
    (frame : ∀ a a1 b b1, a.weights.val.length=64 → b.raw.val.length=64 → b.terms=a.next →
      call a b=ok (.Ok (a1,b1)) →
      a1.weights=a.weights ∧ b1.raw.val.length=64 ∧ b1.terms=a1.next)
    (weights : a.weights.val.length=64) (size : b.raw.val.length=64) (sync : b.terms=a.next)
    (calls : Port2_QueryLoop.Calls call end1 a b out bout n) : bout.terms=out.next := by
  induction calls with
  | done => exact sync
  | step active returned tail ih =>
    have fields := frame _ _ _ _ weights size sync returned
    exact ih (by rw [fields.1]; exact weights) fields.2.1 fields.2.2

theorem loop_terms (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (end1 : Usize)
    (weights : a.weights.val.length=64) (size : b.raw.val.length=64)
    (sync : b.terms=a.next) (bound : a.next.val≤end1.val)
    (h : verifier.candidate.query_loop (Port3_NativeRowFrame.install ops)
      proof p a g obs geometry b end1=ok (.Ok (out,bout))) :
    bout.terms=out.next ∧ bout.terms.val=end1.val := by
  rw [Port3_NativeQueryFrame.loop_eq] at h
  have calls := Port2_QueryLoop.source_calls
    (verifier.candidate.query_values (Port3_NativeRowFrame.install ops))
    proof p g obs geometry end1
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields (Port3_NativeRowFrame.install ops)
      proof p a a1 g obs geometry b b1 h).2.2) a out b bout bound h
  have terms := calls_terms _ _ _ _ _ _ _
    (fun a a1 b b1 hw hs ht h =>
      ⟨(Port3_NativeQueryRaw.query_raw ops proof p a a1 g obs geometry b b1 hw hs h).1,
        (Port3_NativeQueryRaw.query_raw ops proof p a a1 g obs geometry b b1 hw hs h).2,
        query_terms ops proof p a a1 g obs geometry b b1 hw hs ht h⟩)
    weights size sync calls
  exact ⟨terms,by rw [terms]; exact Port2_QueryLoop.returned_next _ _ _ _ _ _ _ calls⟩

#print axioms loop_terms

#print axioms query_terms
#print axioms calls_terms
end AspisR1.Port3_NativeQueryTerms
end
