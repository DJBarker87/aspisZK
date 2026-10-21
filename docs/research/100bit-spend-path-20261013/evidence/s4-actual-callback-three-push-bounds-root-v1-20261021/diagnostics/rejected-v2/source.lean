import S4EbyKCountBoundsRootV1
import EbyKNewToPushStateABI
import FourDotsActualTailLoopTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTailAcceptedTraceRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1 (Contribution InputWitness)
open AspisR1FastDotsActualTailLoopTraceRootV1 (RunTrace)
open AspisR1DotCountBoundV1
abbrev RawFn := AspisR1EbyKPushDotBackend.RawFn
abbrev push (raw : RawFn) := AspisR1EbyKPushDotBackend.pushWithDotBackend raw

def PushBinding (ops : Ops) (raw : RawFn) : Prop :=
  ∀ s v q, ops.ebyKPush s v q=push raw s v q

private theorem unwrap_inner_success (r : core.result.Result Unit Unit) (u : Unit)
    (h : core.result.Result.unwrap core.fmt.DebugUnit r=.ok u) : r=.Ok () := by
  cases r with
  | Ok x => cases x; rfl
  | Err x => cases x; cases h

theorem tail_input_checked_push
    (ops : Ops) (raw : RawFn) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter iter' : AspisR1FastDotsActualTailBodyTraceRootV1.Range)
    (old next : Tail) (c : Contribution)
    (hbinding : PushBinding ops raw)
    (hw : InputWitness ops a g slot iter iter' old next c) :
    push raw old c.coefficient c.scalar=.ok (.Ok (),next) := by
  obtain ⟨slot32,base480,term16,offset,coeffIndex,finish,optQ,pushed,u,
    hnext,h0,h1,h2,h3,h4,hread,h5,hslice,hparse,hunwrap,hpush,hunpush,htail⟩ := hw
  have hr := unwrap_inner_success pushed.1 u hunpush
  have hp : pushed=(.Ok (),next) := Prod.ext hr htail
  rw [hbinding,hp] at hpush
  exact hpush

/-- Actual source tail steps form the existing checked backend trace,
without independent child-push success or count premises. -/
theorem actual_tail_trace_checked_pushes
    (ops : Ops) (raw : RawFn) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : AspisR1FastDotsActualTailBodyTraceRootV1.Range)
    (old out : Tail) (cs : List Contribution)
    (hbinding : PushBinding ops raw)
    (htrace : RunTrace ops a g slot iter old out cs) :
    AcceptedPushTrace raw old (cs.map (fun c=>(c.coefficient,c.scalar))) out := by
  induction htrace with
  | done iter old hbody => exact .nil old
  | @step iter iter' old next out c cs hbody hwitness htail ih =>
      exact .cons old next out c.coefficient c.scalar _
        (tail_input_checked_push ops raw a g slot iter iter' old next c hbinding hwitness) ih

theorem accepted_trace_count_exact (raw : RawFn) (old out : Tail)
    (xs : List (Wide × QM)) (htrace : AcceptedPushTrace raw old xs out) :
    out.count.val=old.count.val+xs.length := by
  induction htrace with
  | nil s => simp only [List.length_nil,Nat.add_zero]
  | @cons s mid out v q xs hpush htail ih =>
      obtain ⟨lo,hi,hlo,hhi,hstate0,hstate1,hcount,hinc,hscalar⟩ :=
        AspisR1EbyKPushDotBackend.successful_push_exact_backend raw s v q mid hpush
      simp only [List.length_cons]
      omega

/-- The actual two-term tail inherits both range invariants and exactly
increments the checked backend count by two. -/
theorem actual_two_term_tail_checked_bounds
    (ops : Ops) (raw : RawFn) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (old out : Tail)
    (hbinding : PushBinding ops raw)
    (h0 : sumsBelowCount old.count.val old.c0.sums)
    (h1 : sumsBelowCount old.count.val old.c1.sums)
    (hcount : old.count.val≤4096)
    (hloop : TailLoop ops {start:=0#usize, «end»:=2#usize} a g slot old=.ok out) :
    ∃ cs, RunTrace ops a g slot {start:=0#usize, «end»:=2#usize} old out cs ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 ∧
      AcceptedPushTrace raw old (cs.map (fun c=>(c.coefficient,c.scalar))) out ∧
      out.count.val=old.count.val+2 ∧
      sumsBelowCount out.count.val out.c0.sums ∧
      sumsBelowCount out.count.val out.c1.sums ∧ out.count.val≤4096 := by
  obtain ⟨cs,htrace,hi,hl⟩ :=
    AspisR1FastDotsActualTailLoopTraceRootV1.actual_two_term_tail_success_trace ops a g slot old out hloop
  have hp := actual_tail_trace_checked_pushes ops raw a g slot _ old out cs hbinding htrace
  have hc := accepted_trace_count_exact raw old out _ hp
  have hb := accepted_trace_preserves_count_bound raw old out _ h0 h1 hcount hp
  simp only [List.length_map,hl] at hc
  exact ⟨cs,htrace,hi,hl,hp,hc,hb⟩

def newFromSource : Result Tail := do
  let state ← AspisR1Stage2Accumulate.new_entry
  .ok (EbyKNewToPushStateABI.stateToPush state)

theorem newFromSource_zero : newFromSource=.ok EbyKNewToPushStateABI.pushZero := by
  obtain ⟨old,hnew,hmap⟩ := EbyKNewToPushStateABI.constructor_new_push_state_compatible
  unfold newFromSource
  rw [hnew]
  simp only [bind_tc_ok,hmap]

private theorem zero_sums_count_bound :
    sumsBelowCount EbyKNewToPushStateABI.pushZero.count.val
      EbyKNewToPushStateABI.pushZero.c0.sums ∧
    sumsBelowCount EbyKNewToPushStateABI.pushZero.count.val
      EbyKNewToPushStateABI.pushZero.c1.sums := by
  constructor <;> intro j hj <;>
    simp [sumsBelowCount,EbyKNewToPushStateABI.pushZero,Array.repeat]

/-- Starting at the source constructor, the actual callback performs exactly
three accepted checked pushes. Their inherited accumulator bounds are
consequences of that same trace, not extra range assumptions. -/
theorem actual_callback_three_checked_pushes
    (ops : Ops) (raw : RawFn) (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (value : Wide) (closure' : Closure)
    (hbinding : PushBinding ops raw) (hnewbinding : ops.ebyKNew=newFromSource)
    (hcall : Callback ops (a,g) slot=.ok (value,closure')) :
    ∃ (wide28 : Wide) (q : QM) (tailOut : Tail)
      (cs : List Contribution),
      Array.index_usize g 28#usize=.ok wide28 ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 ∧
      AcceptedPushTrace raw EbyKNewToPushStateABI.pushZero
        ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))) tailOut ∧
      tailOut.count.val=3 ∧
      sumsBelowCount 3 tailOut.c0.sums ∧ sumsBelowCount 3 tailOut.c1.sums ∧
      (∀ j : Nat, ∀ hj : j<4,
        (tailOut.c0.sums.val[j]'(by rw [tailOut.c0.sums.property]; exact hj)).val<2^46) ∧
      (∀ j : Nat, ∀ hj : j<4,
        (tailOut.c1.sums.val[j]'(by rw [tailOut.c1.sums.property]; exact hj)).val<2^46) := by
  obtain ⟨hclosure,iter,limbs,vals,optBody,body,tail0,wide28,
    slotOffset,start,finish,bytes,optQ,q,pushed,u,tail2,tailValue,
    hstep,hbase,hvals,hbody,hunwrapBody,hnew,hread,hmul,hstart,hfinish,
    hslice,hparse,hunwrap,hpush,hunpush,hloop,hfinishTail,hadd⟩ :=
    actual_callback_success_base_and_tail ops a g slot value closure' hcall
  have hz : tail0=EbyKNewToPushStateABI.pushZero :=
    Result.ok.inj (hnew.symm.trans (hnewbinding.trans newFromSource_zero))
  have hr := unwrap_inner_success pushed.1 u hunpush
  have hp : pushed=(.Ok (),pushed.2) := Prod.ext hr rfl
  have hfirst : push raw EbyKNewToPushStateABI.pushZero wide28 q=.ok (.Ok (),pushed.2) := by
    rw [hbinding,hz,hp] at hpush
    exact hpush
  obtain ⟨cs,htrace,hi,hl⟩ :=
    AspisR1FastDotsActualTailLoopTraceRootV1.actual_two_term_tail_success_trace
      ops a g slot pushed.2 tail2 hloop
  have htail := actual_tail_trace_checked_pushes ops raw a g slot _ pushed.2 tail2 cs hbinding htrace
  have hfull : AcceptedPushTrace raw EbyKNewToPushStateABI.pushZero
      ((wide28,q)::cs.map (fun c=>(c.coefficient,c.scalar))) tail2 :=
    .cons _ pushed.2 tail2 wide28 q _ hfirst htail
  have hc := accepted_trace_count_exact raw EbyKNewToPushStateABI.pushZero tail2 _ hfull
  have hc3 : tail2.count.val=3 := by
    simpa only [List.length_cons,List.length_map,hl,EbyKNewToPushStateABI.pushZero,
      UScalar.val,Nat.zero_add] using hc
  have hb := accepted_trace_preserves_count_bound raw EbyKNewToPushStateABI.pushZero tail2 _
    zero_sums_count_bound.1 zero_sums_count_bound.2 (by decide) hfull
  rw [hc3] at hb
  have h0pre := count_bound_to_preaccumulator 3 tail2.c0.sums (by decide) hb.1
  have h1pre := count_bound_to_preaccumulator 3 tail2.c1.sums (by decide) hb.2.1
  exact ⟨wide28,q,tail2,cs,hread,hi,hl,hfull,hc3,hb.1,hb.2.1,h0pre,h1pre⟩
#print axioms newFromSource_zero
#print axioms actual_callback_three_checked_pushes
#print axioms tail_input_checked_push
#print axioms actual_tail_trace_checked_pushes
#print axioms accepted_trace_count_exact
#print axioms actual_two_term_tail_checked_bounds
end AspisR1FastDotsTailAcceptedTraceRootV1
