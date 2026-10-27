import S4TailLoopForwardRootV1

open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false

namespace AspisR1FastDotsTailLiteralJoinV1

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

def literalPushTrace (ops : Ops) (a : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) : Tail → List Contribution → Result Tail
  | state, [] => .ok state
  | state, c :: cs => do
      let next ← literalPush ops a g slot c.term state
      literalPushTrace ops a g slot next cs

private theorem literalPush_success_of_tailBody_success
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (iter iter' : Range) (old next : Tail)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some term, iter'))
    (hbody : TailBody ops a g slot iter old = .ok (.cont (iter', next))) :
    literalPush ops a g slot term old = .ok next := by
  rw [tailBody_is_literalPush ops a g slot term iter iter' old hnext] at hbody
  cases hp : literalPush ops a g slot term old with
  | ok result =>
      simp only [hp, bind_tc_ok] at hbody
      injection hbody with hstate
      have hresult : result = next := congrArg Prod.snd (ControlFlow.cont.inj hstate)
      subst result
      rfl
  | fail e =>
      simp only [hp, bind_tc_fail] at hbody
      cases hbody
  | div =>
      simp only [hp, bind_tc_div] at hbody
      cases hbody

private theorem input_witness_next
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter iter' : Range) (old next : Tail) (c : Contribution)
    (hw : AspisR1FastDotsActualTailBodyTraceRootV1.InputWitness
      ops a g slot iter iter' old next c) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some c.term, iter') := by
  rcases hw with ⟨_,_,_,_,_,_,_,_,_,hn,_,_,_,_,_,_,_,_,_⟩
  exact hn

private theorem literalPushTrace_of_RunTrace
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : Range) (old out : Tail) (cs : List Contribution)
    (htrace : AspisR1FastDotsActualTailLoopTraceRootV1.RunTrace
      ops a g slot iter old out cs) :
    literalPushTrace ops a g slot old cs = .ok out := by
  induction htrace with
  | done iter old hbody => rfl
  | @step iter iter' old next out c cs hbody hwitness htail ih =>
      have hn := input_witness_next ops a g slot iter iter' old next c hwitness
      have hp := literalPush_success_of_tailBody_success ops a g slot c.term
        iter iter' old next hn hbody
      simp only [literalPushTrace, hp, bind_tc_ok, ih]

private theorem result_bind_ok_id {α : Type} (m : Result α) :
    (do let x ← m; .ok x) = m := by
  cases m <;> rfl

private theorem literalPushTrace_eq_literalTwoPushes_of_indices
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (old : Tail) (cs : List Contribution)
    (hindices : cs.map (fun c => c.term.val) = [0,1]) :
    literalPushTrace ops a g slot old cs = literalTwoPushes ops a g slot old := by
  cases cs with
  | nil =>
      simp only [List.map_nil] at hindices
      cases hindices
  | cons c0 rest =>
      simp only [List.map_cons] at hindices
      have h0v : c0.term.val = 0 := by injection hindices with h _
      have htail : rest.map (fun c => c.term.val) = [1] := by injection hindices with _ h
      cases rest with
      | nil => cases htail
      | cons c1 rest2 =>
          simp only [List.map_cons] at htail
          have h1v : c1.term.val = 1 := by injection htail with h _
          have hlen := congrArg List.length htail
          have hrestlen : rest2.length = 0 := by
            simp only [List.length_cons, List.length_map, List.length_cons, List.length_nil] at hlen
            omega
          cases rest2 with
          | nil =>
              have h0 : c0.term = 0#usize := UScalar.eq_of_val_eq h0v
              have h1 : c1.term = 1#usize := UScalar.eq_of_val_eq h1v
              simp only [literalPushTrace, literalTwoPushes, h0, h1, result_bind_ok_id]
          | cons c2 rest3 =>
              have : False := by simp only [List.length_cons] at hrestlen; omega
              cases this

/-- Every successful original two-step tail loop trace refines to the same
ordered literal pushes and final Tail. The proof follows the actual emitted
body witnesses; P6/Rust standard-library correspondence remains separate. -/
theorem actual_tail_success_implies_literal_two_pushes
    (ops : Ops) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (old out : Tail)
    (hloop : TailLoop ops { start := 0#usize, «end» := 2#usize } a g slot old = .ok out) :
    literalTwoPushes ops a g slot old = .ok out := by
  obtain ⟨cs,htrace,hindices,hlen⟩ :=
    AspisR1FastDotsActualTailLoopTraceRootV1.actual_two_term_tail_success_trace
      ops a g slot old out hloop
  have hrun := literalPushTrace_of_RunTrace ops a g slot
    { start := 0#usize, «end» := 2#usize } old out cs htrace
  have hmodel := literalPushTrace_eq_literalTwoPushes_of_indices
    ops a g slot old cs hindices
  rw [hmodel] at hrun
  exact hrun

#print axioms actual_tail_success_implies_literal_two_pushes

end AspisR1FastDotsTailLiteralJoinV1
