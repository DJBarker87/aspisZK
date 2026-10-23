import Port2_QueryLoop

/-! Field frames from the complete source-shaped query body, independent of
arithmetic correctness. Backend values remain the actual returned values. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_QueryFrame
open Aeneas Aeneas.Std Result AspisR1Stage2

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h

theorem accumulate_weights (ops : AccumulateOps) (p : verifier.Prepared)
    (a out : verifier.Accumulator) (node : Stage2M) (value : Stage2E)
    (b bout : verifier.BatchedWeights)
    (h : verifier.accumulateWithOps ops p a node value b = ok (out,bout)) :
    out.weights = a.weights := by
  unfold verifier.accumulateWithOps at h
  iterate 11 obtain ⟨x, _, h⟩ := bind_success _ _ _ h
  have hp := Result.ok.inj h
  cases hp
  rfl

private theorem guard {T : Type} (b : Bool)
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if b then ok (.Err verifier.Error.Query) else tail) = ok (.Ok out)) :
    tail = ok (.Ok out) := by
  cases b
  · exact h
  · cases h

theorem query_weights (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (h : verifier.candidate.queryWithOps aops ops proof p a g obs geometry b =
      ok (.Ok (out,bout))) : out.weights = a.weights := by
  unfold verifier.candidate.queryWithOps at h
  iterate 25 obtain ⟨x, _, h⟩ := bind_success _ _ _ h
  have h := guard _ _ _ h
  iterate 10 obtain ⟨x, _, h⟩ := bind_success _ _ _ h
  obtain ⟨pair, hacc, h⟩ := bind_success _ _ _ h
  rcases pair with ⟨a1,b1⟩
  obtain ⟨markResult, _, h⟩ := bind_success _ _ _ h
  have hp := Result.ok.inj h
  cases hp
  exact accumulate_weights aops p a out _ _ b bout hacc

theorem calls_weights (call : Port2_QueryLoop.LocalCall) (end1 : Nat)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights) (n : Nat)
    (frame : ∀ a a1 b b1, call a b = ok (.Ok (a1,b1)) → a1.weights = a.weights)
    (calls : Port2_QueryLoop.Calls call end1 a b out bout n) :
    out.weights = a.weights := by
  induction calls with
  | done => rfl
  | step active returned tail ih => exact ih.trans (frame _ _ _ _ returned)

theorem loop_fields (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights) (end1 : Usize)
    (bound : a.next.val ≤ end1.val)
    (h : verifier.candidate.query_loop (verifier.candidate.queryWithOps aops ops)
      proof p a g obs geometry b end1 = ok (.Ok (out,bout))) :
    out.weights = a.weights ∧ out.next.val = end1.val := by
  have calls := Port2_QueryLoop.query_body_calls aops ops proof p g obs geometry
    end1 a out b bout bound h
  exact ⟨calls_weights _ _ _ _ _ _ _
    (fun a a1 b b1 h => query_weights aops ops proof p a a1 g obs geometry b b1 h) calls,
    Port2_QueryLoop.returned_next _ _ _ _ _ _ _ calls⟩

#print axioms bind_success
#print axioms accumulate_weights
#print axioms guard
#print axioms query_weights
#print axioms calls_weights
#print axioms loop_fields
end AspisR1.Port3_QueryFrame
end
