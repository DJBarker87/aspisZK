import Port3_RowsInstall

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_QueryRaw
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_PushFrame (bind_success)

private theorem guard {T : Type} (b : Bool)
    (tail : Result (core.result.Result T verifier.Error)) (out : T)
    (h : (if b then ok (.Err verifier.Error.Query) else tail) = ok (.Ok out)) :
    tail = ok (.Ok out) := by
  cases b
  · exact h
  · cases h

theorem query_raw (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (weights : a.weights.val.length=64) (size : b.raw.val.length=64)
    (h : verifier.candidate.queryWithOps (Port3_RowsInstall.arithmetic aops) ops
      proof p a g obs geometry b = ok (.Ok (out,bout))) :
    out.weights=a.weights ∧ bout.raw.val.length=64 := by
  unfold verifier.candidate.queryWithOps at h
  iterate 25 obtain ⟨x, _, h⟩ := bind_success _ _ _ h
  have h := guard _ _ _ h
  iterate 10 obtain ⟨x, _, h⟩ := bind_success _ _ _ h
  obtain ⟨pair, hacc, h⟩ := bind_success _ _ _ h
  rcases pair with ⟨a1,b1⟩
  obtain ⟨markResult, _, h⟩ := bind_success _ _ _ h
  have hp := Result.ok.inj h
  cases hp
  exact Port3_RowsInstall.accumulate_raw aops p a out _ _ b bout weights size hacc

theorem calls_raw (call : Port2_QueryLoop.LocalCall) (end1 : Nat)
    (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights) (n : Nat)
    (frame : ∀ a a1 b b1, a.weights.val.length=64 → b.raw.val.length=64 →
      call a b = ok (.Ok (a1,b1)) → a1.weights=a.weights ∧ b1.raw.val.length=64)
    (weights : a.weights.val.length=64) (size : b.raw.val.length=64)
    (calls : Port2_QueryLoop.Calls call end1 a b out bout n) :
    out.weights=a.weights ∧ bout.raw.val.length=64 := by
  induction calls with
  | done => exact ⟨rfl,size⟩
  | step active returned tail ih =>
    have step := frame _ _ _ _ weights size returned
    have rest := ih (by rw [step.1]; exact weights) step.2
    exact ⟨rest.1.trans step.1,rest.2⟩

theorem loop_raw (aops : AccumulateOps) (ops : QueryOps)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array Stage2E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights) (end1 : Usize)
    (weights : a.weights.val.length=64) (size : b.raw.val.length=64)
    (bound : a.next.val ≤ end1.val)
    (h : verifier.candidate.query_loop
      (verifier.candidate.queryWithOps (Port3_RowsInstall.arithmetic aops) ops)
      proof p a g obs geometry b end1 = ok (.Ok (out,bout))) :
    out.weights=a.weights ∧ bout.raw.val.length=64 ∧ out.next.val=end1.val := by
  have calls := Port2_QueryLoop.query_body_calls (Port3_RowsInstall.arithmetic aops) ops proof p g obs geometry
    end1 a out b bout bound h
  have frame := calls_raw _ _ _ _ _ _ _
    (fun a a1 b b1 hw hs h => query_raw aops ops proof p a a1 g obs geometry b b1 hw hs h)
    weights size calls
  exact ⟨frame.1,frame.2,Port2_QueryLoop.returned_next _ _ _ _ _ _ _ calls⟩

#print axioms guard
#print axioms query_raw
#print axioms calls_raw
#print axioms loop_raw
end AspisR1.Port3_QueryRaw
end
