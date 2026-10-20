import FourDotsActualTailBodyTraceRootV1
import Mathlib.Data.List.Range
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsActualTailLoopTraceRootV1
open AspisR1FastDotsActualCallbackTailTraceRootV1
open AspisR1FastDotsActualTailBodyTraceRootV1
abbrev U8 := Std.U8
abbrev Range := core.ops.range.Range Usize
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B)
    (v : B) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem next_some_progress (iter iter' : Range) (term : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some term,iter')) :
    term = iter.start ∧ iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val+1 ∧ iter'.end = iter.end := by
  have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) iter
  rw [hnext,WP.spec_ok] at hspec
  by_cases hlt : iter.start.val < iter.end.val
  · simp only [hlt,↓reduceIte] at hspec
    rcases hspec with ⟨⟨hterm,hadvance⟩,hend⟩
    exact ⟨Option.some.inj hterm,hlt,hadvance,hend⟩
  · simp only [hlt,↓reduceIte] at hspec
    rcases hspec with ⟨⟨hnone,_⟩,_⟩
    cases hnone

private theorem loop_success_cases {α β : Type}
    (step : α → Result (ControlFlow α β)) (state : α) (out : β)
    (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧
        Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok flow =>
      cases flow with
      | done result =>
          simp only [hs, bind_tc_ok] at h
          have hresult : result = out := Result.ok.inj h
          subst result
          exact Or.inl rfl
      | cont stateNext =>
          simp only [hs, bind_tc_ok] at h
          exact Or.inr ⟨stateNext, rfl, h⟩

private theorem body_done_identity_and_exhausted
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (old out : Tail)
    (hbody : TailBody ops a g slot iter old = .ok (.done out)) :
    out=old ∧ iter.end.val ≤ iter.start.val := by
  unfold TailBody at hbody
  obtain ⟨⟨optTerm,it⟩,hnext,hrest⟩ := bind_success _ _ _ hbody
  cases optTerm with
  | none =>
      have hout : old=out := ControlFlow.done.inj (Result.ok.inj hrest)
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize) (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter
      rw [hnext,WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · simp only [hlt,↓reduceIte] at hspec
        rcases hspec with ⟨⟨hopt,_⟩,_⟩
        cases hopt
      · exact ⟨hout.symm,by omega⟩
  | some term =>
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

private theorem witness_next
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (old next : Tail) (c : Contribution)
    (h : InputWitness ops a g slot iter iter' old next c) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some c.term,iter') := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hnext,_⟩ := h
  exact hnext

private def tailStep (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize) :
    (Range × Tail) → Result (ControlFlow (Range × Tail) Tail) :=
  fun st => TailBody ops a g slot st.1 st.2

inductive RunTrace (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) : Range → Tail → Tail → List Contribution → Prop where
  | done (iter : Range) (old : Tail)
      (hbody : TailBody ops a g slot iter old = .ok (.done old)) :
      RunTrace ops a g slot iter old old []
  | step {iter iter' : Range} {old next out : Tail} (c : Contribution) (cs : List Contribution)
      (hbody : TailBody ops a g slot iter old = .ok (.cont (iter',next)))
      (hwitness : InputWitness ops a g slot iter iter' old next c)
      (htail : RunTrace ops a g slot iter' next out cs) :
      RunTrace ops a g slot iter old out (c::cs)

/-- The actual emitted tail loop supplies its complete same-state push trace. -/
theorem actual_tail_loop_success_trace
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (old out : Tail)
    (hloop : TailLoop ops iter a g slot old = .ok out) :
    ∃ cs, RunTrace ops a g slot iter old out cs := by
  induction hm : iter.end.val-iter.start.val using Nat.strong_induction_on
      generalizing iter old with
  | h m ih =>
      change Aeneas.Std.loop (tailStep ops a g slot) (iter,old) = .ok out at hloop
      rcases loop_success_cases _ _ _ hloop with hdone | ⟨st',hcont,htail⟩
      · have hb : TailBody ops a g slot iter old = .ok (.done out) := hdone
        have hout := (body_done_identity_and_exhausted ops a g slot iter old out hb).1
        subst out
        exact ⟨[],.done iter old hb⟩
      · rcases st' with ⟨iter',next⟩
        have hb : TailBody ops a g slot iter old = .ok (.cont (iter',next)) := hcont
        obtain ⟨c,hwitness⟩ := actual_tail_body_success_input ops a g slot iter iter' old next hb
        obtain ⟨hterm,hlt,hadvance,hend⟩ := next_some_progress iter iter' c.term
          (witness_next ops a g slot iter iter' old next c hwitness)
        have hdecrease : iter'.end.val-iter'.start.val < m := by rw [hend,hadvance]; omega
        have htail' : TailLoop ops iter' a g slot next = .ok out := htail
        obtain ⟨cs,htrace⟩ := ih _ hdecrease iter' next htail' rfl
        exact ⟨c::cs,.step c cs hb hwitness htrace⟩

/-- The retained tail pushes visit precisely the selected source term range. -/
theorem actual_tail_trace_term_indices
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (old out : Tail) (cs : List Contribution)
    (htrace : RunTrace ops a g slot iter old out cs) :
    cs.map (fun c=>c.term.val) = List.range' iter.start.val (iter.end.val-iter.start.val) := by
  induction htrace with
  | done iter old hbody =>
      have hexhaust := (body_done_identity_and_exhausted ops a g slot iter old old hbody).2
      have hdiff : iter.end.val-iter.start.val=0 := by omega
      simp only [List.map_nil,hdiff,List.range'_zero]
  | @step iter iter' old next out c cs hbody hwitness htail ih =>
      obtain ⟨hterm,hlt,hadvance,hend⟩ := next_some_progress iter iter' c.term
        (witness_next ops a g slot iter iter' old next c hwitness)
      have hdiff : iter.end.val-iter.start.val=(iter'.end.val-iter'.start.val)+1 := by
        rw [hend,hadvance]; omega
      simp only [List.map_cons,ih,hterm,hdiff,List.range'_succ]
      rw [hadvance]

theorem actual_two_term_tail_success_trace
    (ops : Ops) (a : Array U8 608#usize) (g : Array Wide 29#usize) (slot : Usize)
    (old out : Tail)
    (hloop : TailLoop ops {start:=0#usize, «end»:=2#usize} a g slot old = .ok out) :
    ∃ cs, RunTrace ops a g slot {start:=0#usize, «end»:=2#usize} old out cs ∧
      cs.map (fun c=>c.term.val)=[0,1] ∧ cs.length=2 := by
  obtain ⟨cs,htrace⟩ := actual_tail_loop_success_trace ops a g slot _ old out hloop
  have hi := actual_tail_trace_term_indices ops a g slot _ old out cs htrace
  have hi' : cs.map (fun c=>c.term.val)=[0,1] := by simpa using hi
  have hl := congrArg List.length hi'
  simp only [List.length_map,List.length_cons,List.length_nil] at hl
  exact ⟨cs,htrace,hi',hl⟩
#print axioms actual_tail_loop_success_trace
#print axioms actual_tail_trace_term_indices
#print axioms actual_two_term_tail_success_trace
end AspisR1FastDotsActualTailLoopTraceRootV1
