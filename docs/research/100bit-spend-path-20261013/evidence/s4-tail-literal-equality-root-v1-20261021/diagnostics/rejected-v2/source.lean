import S4TailLoopForwardRootV1

open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false

namespace AspisR1FastDotsTailLiteralEqualityRootV1

open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1 (Range TailBody Contribution)
open AspisR1FastDotsTailRangeNextRootV1

/-- The candidate's literal one-tail-push source sequence, parameterized only
by the term index. This preserves the generated operation and error order. -/
def literalPush (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot term : Usize) (old : Tail) : Result Tail := do
  let i ← slot * 32#usize
  let i1 ← 480#usize + i
  let i2 ← term * 16#usize
  let offset ← i1 + i2
  let coeffIndex ← term + 26#usize
  let coefficient ← Array.index_usize g coeffIndex
  let finish ← offset + 16#usize
  let bytes ← core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
    a { start := offset, «end» := finish }
  let optQ ← ops.qm31FromBytes bytes
  let q ← core.option.Option.unwrap optQ
  let (r, next) ← ops.ebyKPush old coefficient q
  core.result.Result.unwrap core.fmt.DebugUnit r
  .ok next

def literalTwoPushes (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (old : Tail) : Result Tail := do
  let tail1 ← literalPush ops a g slot 0#usize old
  literalPush ops a g slot 1#usize tail1

private theorem tailBody_is_literalPush (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot term : Usize) (iter iter' : Range)
    (old : Tail)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some term, iter')) :
    TailBody ops a g slot iter old =
      (literalPush ops a g slot term old >>= fun tailNext =>
        .ok (.cont (iter', tailNext))) := by
  simp [TailBody,
    AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body,
    literalPush, hnext, bind_tc_ok]

/-- Exact equality of all model outcomes; no successful-loop, parser,
coefficient, or accumulator-invariant premise is used. -/
theorem actual_tail_eq_literal_two_pushes
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (old : Tail) :
    TailLoop ops { start := 0#usize, «end» := 2#usize } a g slot old =
      literalTwoPushes ops a g slot old := by
  let r0 : Range := {start:=0#usize,«end»:=2#usize}
  let r1 : Range := {start:=1#usize,«end»:=2#usize}
  let r2 : Range := {start:=2#usize,«end»:=2#usize}
  let step : (Range × Tail) → Result (ControlFlow (Range × Tail) Tail) :=
    fun st => TailBody ops a g slot st.1 st.2
  have hn0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize r0 =
      .ok (some 0#usize,r1) :=
    range_next_succ 0#usize 2#usize 1#usize (by decide) (by decide)
  have hn1 : core.iter.range.IteratorRange.next core.iter.range.StepUsize r1 =
      .ok (some 1#usize,r2) :=
    range_next_succ 1#usize 2#usize 2#usize (by decide) (by decide)
  have hd (tail : Tail) : Aeneas.Std.loop step (r2,tail)=.ok tail := by
    rw [Aeneas.Std.loop.eq_def]
    have hb := actual_tail_body_done ops a g slot 2#usize tail
    simp only [step, r2, hb, bind_tc_ok]
  have hm (tail : Tail) : Aeneas.Std.loop step (r1,tail)=
      literalPush ops a g slot 1#usize tail := by
    rw [Aeneas.Std.loop.eq_def]
    dsimp only [step]
    rw [tailBody_is_literalPush ops a g slot 1#usize r1 r2 tail hn1]
    cases hp : literalPush ops a g slot 1#usize tail with
    | ok next => simp only [hp,bind_tc_ok,hd]
    | fail e => simp only [hp,bind_tc_fail]
    | div => simp only [hp,bind_tc_div]
  change Aeneas.Std.loop step (r0,old)=literalTwoPushes ops a g slot old
  rw [Aeneas.Std.loop.eq_def]
  dsimp only [step]
  rw [tailBody_is_literalPush ops a g slot 0#usize r0 r1 old hn0]
  cases hp : literalPush ops a g slot 0#usize old with
  | ok next => simp only [literalTwoPushes,hp,bind_tc_ok,hm]
  | fail e => simp only [literalTwoPushes,hp,bind_tc_fail]
  | div => simp only [literalTwoPushes,hp,bind_tc_div]

theorem literal_two_pushes_success_actual_tail
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (old out : Tail)
    (h : literalTwoPushes ops a g slot old=.ok out) :
    TailLoop ops { start:=0#usize,«end»:=2#usize } a g slot old=.ok out := by
  rw [actual_tail_eq_literal_two_pushes]
  exact h

#print axioms actual_tail_eq_literal_two_pushes
#print axioms literal_two_pushes_success_actual_tail
end AspisR1FastDotsTailLiteralEqualityRootV1
