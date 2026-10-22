import FourDotsActualCallbackTailTraceRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTailBodyTraceRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
abbrev U8 := Std.U8
abbrev Range := core.ops.range.Range Usize
abbrev TailBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop1.body

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

structure Contribution where
  term : Usize
  coefficient : Wide
  bytes : Slice U8
  scalar : QM

def InputWitness (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter iter' : Range) (old next : Tail) (c : Contribution) : Prop :=
  ∃ (slot32 base480 term16 offset coeffIndex finish : Usize)
    (optQ : Option QM) (pushed : core.result.Result Unit Unit × Tail) (u : Unit),
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some c.term,iter') ∧
    (slot*32#usize : Result Usize) = .ok slot32 ∧
    (480#usize+slot32 : Result Usize) = .ok base480 ∧
    (c.term*16#usize : Result Usize) = .ok term16 ∧
    (base480+term16 : Result Usize) = .ok offset ∧
    (c.term+26#usize : Result Usize) = .ok coeffIndex ∧
    Array.index_usize g coeffIndex = .ok c.coefficient ∧
    (offset+16#usize : Result Usize) = .ok finish ∧
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      a {start:=offset, «end»:=finish} = .ok c.bytes ∧
    ops.qm31FromBytes c.bytes = .ok optQ ∧ core.option.Option.unwrap optQ = .ok c.scalar ∧
    ops.ebyKPush old c.coefficient c.scalar = .ok pushed ∧
    core.result.Result.unwrap core.fmt.DebugUnit pushed.1 = .ok u ∧ pushed.2=next

/-- A successful source tail body retains the actual coefficient index,
checked byte offsets, parser and accumulator push, all from the same step. -/
theorem actual_tail_body_success_input
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (old next : Tail)
    (hbody : TailBody ops a g slot iter old = .ok (.cont (iter',next))) :
    ∃ c : Contribution, InputWitness ops a g slot iter iter' old next c := by
  unfold TailBody at hbody
  obtain ⟨⟨optTerm,it⟩,hnext,hrest⟩ := bind_success _ _ _ hbody
  cases optTerm with
  | none => cases Result.ok.inj hrest
  | some term =>
      obtain ⟨slot32,h0,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨base480,h1,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨term16,h2,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨offset,h3,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨coeffIndex,h4,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨coefficient,hread,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨finish,h5,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨bytes,hslice,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨optQ,hparse,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨scalar,hunwrap,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨pushed,hpush,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨u,hunpush,hrest⟩ := bind_success _ _ _ hrest
      have hp : (it,pushed.2)=(iter',next) := ControlFlow.cont.inj (Result.ok.inj hrest)
      have hit : it=iter' := congrArg Prod.fst hp
      have htail : pushed.2=next := congrArg Prod.snd hp
      refine ⟨⟨term,coefficient,bytes,scalar⟩,
        slot32,base480,term16,offset,coeffIndex,finish,optQ,pushed,u,
        ?_,h0,h1,h2,h3,h4,hread,h5,hslice,hparse,hunwrap,hpush,hunpush,htail⟩
      simpa only [hit] using hnext

#print axioms actual_tail_body_success_input
end AspisR1FastDotsActualTailBodyTraceRootV1
