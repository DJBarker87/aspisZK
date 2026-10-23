import Port4C_QueryValues
import Port3_NativeWriterShape

/-! The pending constructor resets terms to zero in BOTH blocks. TX2 starts
next10, so its correct invariant is terms=next-10, not terms=next. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_QueryCounters
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

theorem query_increment (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (weights : a.weights.val.length=64)
    (size : b.raw.val.length=64) (small : b.terms.val<256)
    (h : verifier.candidate.query_values (Port3_NativeRowFrame.install ops)
      proof p a g obs geometry b=ok (.Ok (out,bout))) :
    bout.terms.val=b.terms.val+1 := by
  obtain ⟨o⟩ := Port4C_QueryValues.observed (Port3_NativeRowFrame.install ops)
    proof p a out g obs geometry b bout h
  rw [Port3_NativeTerms.accumulate_terms ops p a out o.node o.value b bout weights size o.accumulate]
  exact Port3_Wrapping.increment b.terms small

theorem calls_count (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (end1 : Nat)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights) (n : Nat)
    (weights : a.weights.val.length=64) (size : b.raw.val.length=64)
    (small : b.terms.val+n<256)
    (calls : Port2_QueryLoop.Calls
      (fun a b => verifier.candidate.query_values (Port3_NativeRowFrame.install ops)
        proof p a g obs geometry b) end1 a b out bout n) :
    bout.terms.val=b.terms.val+n := by
  induction calls with
  | done => omega
  | @step a b a1 b1 n active returned tail ih =>
    have raw := Port3_NativeQueryRaw.query_raw ops proof p a a1 g obs geometry b b1 weights size returned
    have inc := query_increment ops proof p a a1 g obs geometry b b1 weights size (by omega) returned
    have count := ih (by rw [raw.1]; exact weights) raw.2 (by omega)
    omega

/-- Exact term count for either interval; the same loop supplies all calls. -/
theorem loop_count (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights) (end1 : Usize)
    (weights : a.weights.val.length=64) (size : b.raw.val.length=64)
    (bound : a.next.val≤end1.val) (small : b.terms.val+(end1.val-a.next.val)<256)
    (h : verifier.candidate.query_loop (Port3_NativeRowFrame.install ops)
      proof p a g obs geometry b end1=ok (.Ok (out,bout))) :
    bout.terms.val=b.terms.val+(end1.val-a.next.val) ∧ out.next.val=end1.val := by
  rw [Port3_NativeQueryFrame.loop_eq] at h
  have calls := Port2_QueryLoop.source_calls
    (verifier.candidate.query_values (Port3_NativeRowFrame.install ops))
    proof p g obs geometry end1
    (fun a a1 b b1 h => (Port3_NativeQueryFrame.query_fields (Port3_NativeRowFrame.install ops)
      proof p a a1 g obs geometry b b1 h).2.2) a out b bout bound h
  exact ⟨calls_count ops proof p g obs geometry end1.val a out b bout _ weights size small calls,
    Port2_QueryLoop.returned_next _ _ _ _ _ _ _ calls⟩

#print axioms query_increment
#print axioms calls_count
#print axioms loop_count
end AspisR1.Port4C_QueryCounters
end
