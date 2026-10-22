import NewOuterLimbLoopSegmentV1
import FourDotsBatchBodyAdvanceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsFixedHeadLoopTransferRootV1
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

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

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

theorem fixed_body_done_old_body
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs out : Array U64 8#usize)
    (hbody : NewBody ops q g slot iter limbs=.ok (.done out)) :
    OldBody ops q g slot iter limbs=.ok (.done out) := by
  unfold NewBody AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0.body at hbody
  obtain ⟨⟨o,it⟩,hnext,hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
    have he : limbs=out := ControlFlow.done.inj (Result.ok.inj hrest)
    subst out
    simp only [OldBody,
      AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0.body,
      hnext,bind_tc_ok]
  | some start =>
    repeat' (first | obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest)
    cases Result.ok.inj hrest

private def newStep (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) : (StepBy × Array U64 8#usize) →
      Result (ControlFlow (StepBy × Array U64 8#usize) (Array U64 8#usize)) :=
  fun st => NewBody ops q g slot st.1 st.2
private def oldStep (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) : (StepBy × Array U64 8#usize) →
      Result (ControlFlow (StepBy × Array U64 8#usize) (Array U64 8#usize)) :=
  fun st => OldBody ops q g slot st.1 st.2

/-- A successful complete fixed-call head loop transfers to the original
head loop with identical iterators, inputs and returned limb array. The
existing eight-step body bridge supplies the arithmetic correspondence. -/
theorem fixed_head_loop_success_old_head_loop
    (ops : Ops) (q : Array U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : StepBy) (limbs out : Array U64 8#usize)
    (hcount : ops.wideLimbCount=.ok 8#usize) (hstep : iter.step_by=4#usize)
    (hloop : NewLoop ops iter q g slot limbs=.ok out) :
    OldLoop ops iter q g slot limbs=.ok out := by
  induction hm : iter.iter.end.val-iter.iter.start.val using Nat.strong_induction_on
      generalizing iter limbs with
  | h m ih =>
    change loop (newStep ops q g slot) (iter,limbs)=.ok out at hloop
    rcases loop_success_cases _ _ _ hloop with hdone | ⟨st',hcont,htail⟩
    · have hbody : NewBody ops q g slot iter limbs=.ok (.done out) := by
        simpa only [newStep] using hdone
      have hb := fixed_body_done_old_body ops q g slot iter limbs out hbody
      change loop (oldStep ops q g slot) (iter,limbs)=.ok out
      rw [loop.eq_def]
      simpa only [oldStep,hb,bind_tc_ok]
    · rcases st' with ⟨iter',limbs'⟩
      have hbody : NewBody ops q g slot iter limbs=.ok (.cont (iter',limbs')) := by
        simpa only [newStep] using hcont
      have hb := AspisR1FastDotsNewOuterLimbLoopSegmentV1.fixed_batch_body_success_old_body
        ops q g slot iter iter' limbs limbs' hcount hbody
      obtain ⟨start,hnext,hstartEq,hcursor,hend,hstep'⟩ :=
        AspisR1FastDotsBatchBodyAdvance.body_success_cont_step
          ops q g slot iter iter' limbs limbs' hstep hb
      have hpositive : iter.step_by.val>0 := by rw [hstep]; decide
      have hspec := core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpositive
      rw [hnext,WP.spec_ok] at hspec
      have hlt : iter.iter.start.val<iter.iter.end.val := by
        by_contra hnot
        simp only [hnot,↓reduceIte] at hspec
        rcases hspec with ⟨⟨hnone,_⟩,_,_⟩
        cases hnone
      have hdec : iter'.iter.end.val-iter'.iter.start.val<m := by
        rw [hend,hcursor]
        by_cases hmin : iter.iter.start.val+iter.step_by.val≤iter.iter.end.val
        · rw [Nat.min_eq_left hmin]
          omega
        · rw [Nat.min_eq_right (by omega)]
          omega
      have ht := ih _ hdec iter' limbs' (hstep'.trans hstep) htail rfl
      change loop (oldStep ops q g slot) (iter,limbs)=.ok out
      rw [loop.eq_def]
      simpa only [oldStep,hb,bind_tc_ok] using ht

#print axioms fixed_body_done_old_body
#print axioms fixed_head_loop_success_old_head_loop
end AspisR1FastDotsFixedHeadLoopTransferRootV1
