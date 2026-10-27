import Port3_NativeQueryFrame
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBB_QueryTrace
open AspisR1Stage2
abbrev Acc := verifier.Accumulator
abbrev BW := verifier.BatchedWeights
abbrev State := core.result.Result (Acc × BW) verifier.Error
abbrev Call := Acc → BW → Result State
/-- Complete local driver trace, including a rejected or failed last call.
No whole-loop output equality is a field of this relation. -/
inductive Trace (call : Call) (end1 : Nat) : State → Result State → Prop
 | error (e : verifier.Error) : Trace call end1 (.Err e) (ok (.Err e))
 | stop (a : Acc) (b : BW) (done : end1≤a.next.val) :
   Trace call end1 (.Ok (a,b)) (ok (.Ok (a,b)))
 | step {a : Acc} {b : BW} {reply : State} {out : Result State}
   (active : a.next.val<end1) (head : call a b=ok reply)
   (tail : Trace call end1 reply out) : Trace call end1 (.Ok (a,b)) out
 | fail {a : Acc} {b : BW} (active : a.next.val<end1) (e : Aeneas.Std.Error)
   (head : call a b=Result.fail e) : Trace call end1 (.Ok (a,b)) (Result.fail e)
 | div {a : Acc} {b : BW} (active : a.next.val<end1)
   (head : call a b=Result.div) : Trace call end1 (.Ok (a,b)) Result.div

theorem unroll (call : QueryCall) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (state : State) :
 verifier.candidate.query_loop_loop call state proof p g obs geo end1=
 match state with
 | .Err e => ok (.Err e)
 | .Ok (a,b) => if end1.val≤a.next.val then ok (.Ok (a,b)) else
   (do let reply ← call proof p a g obs geo b
       verifier.candidate.query_loop_loop call reply proof p g obs geo end1) := by
 unfold verifier.candidate.query_loop_loop
 rw [Aeneas.Std.loop.eq_def]
 cases state with
 | Err e => rfl
 | Ok pair =>
  rcases pair with ⟨a,b⟩
  unfold verifier.candidate.query_loop_loop.body
  split <;> rfl

/-- Every linked local callback trace gives the complete cohort Result,
including first rejection, failure or divergence. -/
theorem native_result (call : QueryCall) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (state : State) (out : Result State)
 (trace : Trace (fun a b => call proof p a g obs geo b) end1.val state out) :
 verifier.candidate.query_loop_loop call state proof p g obs geo end1=out := by
 induction trace with
 | error e => rw [unroll]
 | stop a b done => rw [unroll,if_pos done]
 | step active head tail ih => rw [unroll,if_neg (by omega),head,bind_tc_ok];exact ih
 | fail active e head => rw [unroll,if_neg (by omega),head,bind_tc_fail]
 | div active head => rw [unroll,if_neg (by omega),head,bind_tc_div]

#print axioms unroll
#print axioms native_result
end NBB_QueryTrace
