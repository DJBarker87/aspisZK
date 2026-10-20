import FourDotsActualTermBodyLinearBoundV1
import Aeneas.Std.RangeIter
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualTermLoopLinearBoundV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Range := core.ops.range.Range Usize
abbrev cap := AspisR1FastDotsActualInnerLoopLinearBoundV1.cap
abbrev cell := AspisR1FastDotsActualInnerLoopLinearBoundV1.cell
abbrev TermBody := AspisR1FastDotsActualTermBodyLinearBoundV1.TermBody
abbrev TermLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private def termStep (ops : Ops) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) :
    (Range × Array U64 8#usize) → Result (ControlFlow (Range × Array U64 8#usize)
      (Array U64 8#usize)) :=
  fun st => TermBody ops a a1 slot st.1 st.2

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

private theorem term_body_cont_progress (ops : Ops)
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : TermBody ops a a1 slot iter sums = .ok (.cont (iter', sums'))) :
    iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  unfold TermBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some term =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨sumsFinal, _, hrest⟩ := bind_success _ _ _ hrest
      have hpair : (iter1, sumsFinal) = (iter', sums') :=
        ControlFlow.cont.inj (Result.ok.inj hrest)
      have hiter : iter1 = iter' := congrArg Prod.fst hpair
      have hclone : ∀ x : Usize, core.clone.CloneUsize.clone x = .ok x := by
        intro x
        rfl
      have hltSpec : ∀ x y : Usize,
          core.cmp.PartialOrdUsize.lt x y = .ok (decide (x.val < y.val)) := by
        intros
        rfl
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize) hclone hltSpec iter
      rw [hnext, WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · simp only [hlt, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨_, hadvance⟩, hend⟩
        subst iter'
        exact ⟨hlt, hadvance, hend⟩
      · simp only [hlt, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨hnone, _⟩, _⟩
        cases hnone

private theorem term_body_done_identity (ops : Ops)
    (a : Array U8 608#usize) (a1 : Array Wide 29#usize) (slot : Usize)
    (iter : Range) (sums out : Array U64 8#usize)
    (hbody : TermBody ops a a1 slot iter sums = .ok (.done out)) : out = sums := by
  unfold TermBody at hbody
  obtain ⟨⟨o, iter1⟩, _, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      change Result.ok (ControlFlow.done sums) = Result.ok (ControlFlow.done out) at hrest
      exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some _ =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

/-- A successful emitted term-range loop adds at most one cap per visited
    term. For a range containing at most `d` entries and a k-cap input, the
    output is bounded by `(k+d)*cap`; this is the exact 4-term batch envelope
    when `k=0`, `d≤4`. -/
theorem term_loop_success_linear_bound
    (ops : Ops) (k : Nat) (a : Array U8 608#usize)
    (a1 : Array Wide 29#usize) (slot : Usize) (iter : Range)
    (sums out : Array U64 8#usize) (d : Nat)
    (hcoord : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (a1.val[i.val]'(by simpa [a1.property] using i.isLt)))
    (hinput : ∀ i : Fin 8, cell sums i ≤ k * cap)
    (hsize : iter.end.val - iter.start.val ≤ d)
    (hbudget : k + d ≤ 4)
    (hloop : TermLoop (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
        iter a a1 slot sums = .ok out) :
    ∀ i : Fin 8, cell out i ≤ (k + d) * cap := by
  induction hm : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter sums k d with
  | h m ih =>
      change Aeneas.Std.loop (termStep
        (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops) a a1 slot)
        (iter, sums) = .ok out at hloop
      rcases loop_success_cases _ _ _ hloop with hdone | ⟨st', hcont, htail⟩
      · have hbody : TermBody
            (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
            a a1 slot iter sums = .ok (.done out) := by
          simpa [termStep] using hdone
        have hout := term_body_done_identity _ _ _ _ _ _ _ hbody
        subst out
        intro i
        have hkd : k ≤ k + d := by omega
        exact le_trans (hinput i) (Nat.mul_le_mul_right cap hkd)
      · rcases st' with ⟨iter', sums'⟩
        have hbody : TermBody
            (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
            a a1 slot iter sums = .ok (.cont (iter', sums')) := by
          simpa [termStep] using hcont
        obtain ⟨hlt, hadvance, hend⟩ := term_body_cont_progress
          (AspisR1FastDotsActualTermBodyLinearBoundV1.withCurrentTermBodyOps ops)
          a a1 slot iter iter' sums sums' hbody
        have hdist : iter'.end.val - iter'.start.val + 1 = iter.end.val - iter.start.val := by
          rw [hend, hadvance]
          omega
        have hdist' : iter'.end.val - iter'.start.val =
            iter.end.val - iter.start.val - 1 := by omega
        have hdpos : 0 < iter.end.val - iter.start.val := by omega
        have hk3 : k ≤ 3 := by omega
        have hsum' : ∀ i : Fin 8, cell sums' i ≤ (k + 1) * cap :=
          AspisR1FastDotsActualTermBodyLinearBoundV1.current_term_body_success_linear_bound
            ops k hk3 a a1 slot iter iter' sums sums' hcoord hinput hbody
        have hsize' : iter'.end.val - iter'.start.val ≤ d - 1 := by omega
        have hbudget' : (k + 1) + (d - 1) ≤ 4 := by omega
        have htail' := ih (iter.end.val - iter.start.val - 1) (by omega)
          (k + 1) iter' sums' (d - 1) hsum' hsize' hbudget' htail hdist'
        intro i
        have hsameMeasure : k + d = (k + 1) + (d - 1) := by omega
        rw [hsameMeasure]
        exact htail' i

#print axioms term_loop_success_linear_bound

end AspisR1FastDotsActualTermLoopLinearBoundV1
