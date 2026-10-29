import Port3_NativeQueryFrame
import Port2_QueryLoop
set_option autoImplicit false
noncomputable section
namespace NEB_QueryCallRanges
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
open Port3_NativeQueryBody
abbrev Acc := verifier.Accumulator
abbrev BW := verifier.BatchedWeights

inductive Every (call : Port2_QueryLoop.LocalCall) (finish : Nat)
    (P : Acc → BW → Prop) : Acc → BW → Acc → BW → Nat → Prop
  | done (a : Acc) (b : BW) (atEnd : a.next.val=finish) : Every call finish P a b a b 0
  | step {a a1 out : Acc} {b b1 bout : BW} {n : Nat}
      (active : a.next.val<finish) (returned : call a b=ok (.Ok (a1,b1)))
      (domain : P a b) (tail : Every call finish P a1 b1 out bout n) :
      Every call finish P a b out bout (n+1)

/-- An actual successful call sequence inherits the geometry accessor's full
index domain at each reached call. Nothing selects a fresh intermediate run. -/
theorem calls {call : Port2_QueryLoop.LocalCall} {finish : Nat}
    (advance : ∀ a a1 b b1,call a b=ok (.Ok (a1,b1)) → a1.next.val=a.next.val+1)
    (geometry : verifier.QueryGeometry)
    (length : geometry.inverses.val.length=finish-geometry.start.val)
    (zlength : geometry.line_z.val.length=finish-geometry.start.val)
    (cap : finish≤22) {a out : Acc} {b bout : BW} {n : Nat}
    (trace : Port2_QueryLoop.Calls call finish a b out bout n)
    (lower : geometry.start.val≤a.next.val) :
    Every call finish (fun current _ =>
      geometry.start.val≤current.next.val ∧ current.next.val<finish ∧
      current.next.val<22 ∧
      current.next.val-geometry.start.val<geometry.inverses.val.length ∧
      current.next.val-geometry.start.val<geometry.line_z.val.length) a b out bout n := by
  induction trace with
  | done a b atEnd => exact .done a b atEnd
  | @step a a1 out b b1 bout n active returned tail ih =>
    have next := advance a a1 b b1 returned
    exact .step active returned (by omega) (ih (by omega))

/-- Concrete cohort root instantiated with its own query_values body. This is
an accepted-run range certificate, not native root refinement. -/
theorem root (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a out : Acc) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
    (b bout : BW) (finish : Usize)
    (lower : geometry.start.val≤a.next.val) (upper : a.next.val≤finish.val)
    (length : geometry.inverses.val.length=finish.val-geometry.start.val)
    (zlength : geometry.line_z.val.length=finish.val-geometry.start.val)
    (cap : finish.val≤22)
    (accepted : verifier.candidate.query_loop ops proof p a g obs geometry b finish=ok (.Ok (out,bout))) :
    Every (fun a b => verifier.candidate.query_values ops proof p a g obs geometry b)
      finish.val (fun current _ =>
        geometry.start.val≤current.next.val ∧ current.next.val<finish.val ∧
        current.next.val<22 ∧
        current.next.val-geometry.start.val<geometry.inverses.val.length ∧
        current.next.val-geometry.start.val<geometry.line_z.val.length)
      a b out bout (finish.val-a.next.val) := by
  have advance := fun a a1 b b1 h =>
    (Port3_NativeQueryFrame.query_fields ops proof p a a1 g obs geometry b b1 h).2.2
  rw [Port3_NativeQueryFrame.loop_eq] at accepted
  have trace := Port2_QueryLoop.source_calls _ proof p g obs geometry finish advance
    a out b bout upper accepted
  exact calls advance geometry length zlength cap trace lower

#print axioms calls
#print axioms root
end NEB_QueryCallRanges
end
