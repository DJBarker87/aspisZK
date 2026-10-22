import AspisR1FastDotsCurrent.FunsOpsFixedV6
import FourDotsBatchBodyAdvanceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsReverseOuterHeadLoopRootV1
abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := Std.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev StepBy := AspisR1FastDotsBatchBodyAdvance.StepBy
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev NewBody := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0.body
abbrev NewLoop := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0
abbrev OldBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body
abbrev OldLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0

private theorem loop_success_cases {α β : Type}
    (step : α → Result (ControlFlow α β)) (state : α) (out : β)
    (h : loop step state=.ok out) :
    step state=.ok (.done out) ∨
      ∃ stateNext, step state=.ok (.cont stateNext) ∧ loop step stateNext=.ok out := by
  rw [loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok flow =>
    cases flow with
    | done result =>
      simp only [hs,bind_tc_ok] at h
      have heq : result=out := Result.ok.inj h
      subst result
      exact Or.inl rfl
    | cont next =>
      simp only [hs,bind_tc_ok] at h
      exact Or.inr ⟨next,rfl,h⟩

private def newStep (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) : (StepBy × Array U64 8#usize) →
      Result (ControlFlow (StepBy × Array U64 8#usize) (Array U64 8#usize)) :=
  fun st => NewBody ops q g slot st.1 st.2
private def oldStep (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) : (StepBy × Array U64 8#usize) →
      Result (ControlFlow (StepBy × Array U64 8#usize) (Array U64 8#usize)) :=
  fun st => OldBody ops q g slot st.1 st.2

/-- Reverse successful complete head-loop transport. Only the successful
body law remains explicit; the outer StepBy progress and termination trace
are derived from the original generated body and its checked iterator. -/
theorem old_head_loop_success_fixed_head_loop
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs out : Array U64 8#usize)
    (hbodyLaw : ∀ (cursor : StepBy) (state : Array U64 8#usize)
      (flow : ControlFlow (StepBy × Array U64 8#usize) (Array U64 8#usize)),
      cursor.step_by=4#usize →
      OldBody ops q g slot cursor state=.ok flow →
      NewBody ops q g slot cursor state=.ok flow)
    (hstep : iter.step_by=4#usize)
    (hloop : OldLoop ops iter q g slot limbs=.ok out) :
    NewLoop ops iter q g slot limbs=.ok out := by
  induction hm : iter.iter.end.val-iter.iter.start.val using Nat.strong_induction_on
      generalizing iter limbs with
  | h m ih =>
    change loop (oldStep ops q g slot) (iter,limbs)=.ok out at hloop
    rcases loop_success_cases _ _ _ hloop with hdone | ⟨st',hcont,htail⟩
    · have hbody : OldBody ops q g slot iter limbs=.ok (.done out) := by
        simpa only [oldStep] using hdone
      have hb := hbodyLaw iter limbs (.done out) hstep hbody
      change loop (newStep ops q g slot) (iter,limbs)=.ok out
      rw [loop.eq_def]
      simpa only [newStep,hb,bind_tc_ok]
    · rcases st' with ⟨iter',limbs'⟩
      have hbody : OldBody ops q g slot iter limbs=.ok (.cont (iter',limbs')) := by
        simpa only [oldStep] using hcont
      have hb := hbodyLaw iter limbs (.cont (iter',limbs')) hstep hbody
      obtain ⟨start,hnext,hstartEq,hcursor,hend,hstep'⟩ :=
        AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
          ops q g slot iter iter' limbs limbs' hstep hbody
      have hpositive : iter.step_by.val>0 := by rw [hstep]; decide
      have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpositive
      rw [hnext,WP.spec_ok] at hspec
      have hlt : iter.iter.start.val < iter.iter.end.val := by
        by_contra hnot
        simp only [hnot,↓reduceIte] at hspec
        rcases hspec with ⟨⟨hnone,_⟩,_,_⟩
        cases hnone
      have hdec : iter'.iter.end.val-iter'.iter.start.val < m := by
        rw [hend,hcursor]
        by_cases hmin : iter.iter.start.val+iter.step_by.val ≤ iter.iter.end.val
        · rw [Nat.min_eq_left hmin]
          omega
        · rw [Nat.min_eq_right (by omega)]
          omega
      have ht := ih _ hdec iter' limbs' (hstep'.trans hstep) htail rfl
      change loop (newStep ops q g slot) (iter',limbs')=.ok out at ht
      change loop (newStep ops q g slot) (iter,limbs)=.ok out
      rw [loop.eq_def]
      simpa only [newStep,hb,bind_tc_ok] using ht


#print axioms old_head_loop_success_fixed_head_loop
end AspisR1FastDotsReverseOuterHeadLoopRootV1
