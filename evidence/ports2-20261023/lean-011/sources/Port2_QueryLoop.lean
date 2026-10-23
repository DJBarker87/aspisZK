import Port2_QueryAdvance
import Port2_ReturnedState

/-! Exact successful call sequence for both source loop ranges. This extends
control-flow coverage to TX1's end=10; the full opening/fold/row interpretation
is deliberately not inferred from a successful loop. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port2_QueryLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2
abbrev Acc := verifier.Accumulator
abbrev BW := verifier.BatchedWeights
abbrev LocalCall := Acc → BW → Result (core.result.Result (Acc × BW) verifier.Error)

inductive Calls (call : LocalCall) (end1 : Nat) : Acc → BW → Acc → BW → Nat → Prop
  | done (a : Acc) (b : BW) (atEnd : a.next.val = end1) : Calls call end1 a b a b 0
  | step {a a1 out : Acc} {b b1 bout : BW} {n : Nat}
      (active : a.next.val < end1) (returned : call a b = ok (.Ok (a1,b1)))
      (tail : Calls call end1 a1 b1 out bout n) : Calls call end1 a b out bout (n+1)

theorem error_stops (call : QueryCall) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (end1 : Usize) (e : verifier.Error) :
    verifier.candidate.query_loop_loop call (.Err e) proof p g obs geometry end1 = ok (.Err e) := by
  unfold verifier.candidate.query_loop_loop
  rw [Aeneas.Std.loop.eq_def]
  rfl

/-- No independently selected intermediate states: every constructor carries
an actual successful call, in order, from the same source loop. -/
theorem source_calls (call : QueryCall) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (end1 : Usize)
    (advance : ∀ a a1 b b1, call proof p a g obs geometry b = ok (.Ok (a1,b1)) →
      a1.next.val = a.next.val+1)
    (a out : Acc) (b bout : BW) (bound : a.next.val ≤ end1.val)
    (success : verifier.candidate.query_loop call proof p a g obs geometry b end1 = ok (.Ok (out,bout))) :
    Calls (fun a b => call proof p a g obs geometry b) end1.val a b out bout (end1.val-a.next.val) := by
  change verifier.candidate.query_loop_loop call (.Ok (a,b)) proof p g obs geometry end1 = _ at success
  induction fuel : end1.val-a.next.val generalizing a b with
  | zero =>
    have he : a.next.val = end1.val := by omega
    unfold verifier.candidate.query_loop_loop at success
    rw [Aeneas.Std.loop.eq_def] at success
    have pair : a = out ∧ b = bout := by
      simpa [verifier.candidate.query_loop_loop.body,he] using success
    rcases pair with ⟨rfl,rfl⟩
    exact .done a b he
  | succ n ih =>
    have active : a.next.val < end1.val := by omega
    have inactive : ¬ end1.val ≤ a.next.val := Nat.not_le.mpr active
    unfold verifier.candidate.query_loop_loop at success
    rw [Aeneas.Std.loop.eq_def] at success
    simp only [verifier.candidate.query_loop_loop.body] at success
    cases hc : call proof p a g obs geometry b with
    | fail e => simp [hc,inactive] at success
    | div => simp [hc,inactive] at success
    | ok r =>
      have tail : verifier.candidate.query_loop_loop call r proof p g obs geometry end1 = ok (.Ok (out,bout)) := by
        simpa [hc,inactive,verifier.candidate.query_loop_loop] using success
      cases r with
      | Err e => rw [error_stops] at tail; cases tail
      | Ok pair =>
        rcases pair with ⟨a1,b1⟩
        have hn := advance a a1 b b1 hc
        have rest : Calls (fun a b => call proof p a g obs geometry b) end1.val a1 b1 out bout n := by
          apply ih a1 b1 (by omega) tail (by omega)
        exact .step active hc rest

/-- Instantiated with the source-shaped opening/fold/accumulate body. Its
next-step law is discharged by source inversion, not a new row assumption. -/
theorem query_body_calls (aops : AccumulateOps) (ops : QueryOps) (proof : Slice U8)
    (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (end1 : Usize) (a out : Acc) (b bout : BW) (bound : a.next.val ≤ end1.val)
    (success : verifier.candidate.query_loop (verifier.candidate.queryWithOps aops ops)
      proof p a g obs geometry b end1 = ok (.Ok (out,bout))) :
    Calls (fun a b => verifier.candidate.queryWithOps aops ops proof p a g obs geometry b)
      end1.val a b out bout (end1.val-a.next.val) :=
  source_calls _ proof p g obs geometry end1
    (fun a a1 b b1 h => query_next aops ops proof p a a1 g obs geometry b b1 h)
    a out b bout bound success

theorem returned_next (call : LocalCall) (end1 : Nat)
    (a out : Acc) (b bout : BW) (n : Nat) (calls : Calls call end1 a b out bout n) :
    out.next.val = end1 := by
  induction calls with
  | done a b h => exact h
  | step active returned tail ih => exact ih

#print axioms error_stops
#print axioms source_calls
#print axioms query_body_calls
#print axioms returned_next
end AspisR1.Port2_QueryLoop
end
