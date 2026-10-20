import FourDotsActualLimbPrefixStepV3
import Aeneas.Std.RangeIter
import Aeneas.Std.Array.Array
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualInnerLoopBoundV1

abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := Std.U32
abbrev Range := core.ops.range.Range Usize
abbrev InnerBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0.body
abbrev InnerLoop := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0
abbrev cap : Nat := AspisR1FastDotsActualLimbPrefixStepV3.cap

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private def innerStep (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) :
    (Range × Array U64 8#usize × AspisR1FastDotsCurrent.aspis_core.field.M31) →
      Result (ControlFlow
        (Range × Array U64 8#usize × AspisR1FastDotsCurrent.aspis_core.field.M31)
        (Array U64 8#usize)) :=
  fun s => InnerBody ops coeff s.1 s.2.1 s.2.2

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

private theorem body_done_eq_sums
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) (iter : Range)
    (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbody : InnerBody ops coeff iter sums scalar = .ok (.done out)) : out = sums := by
  unfold InnerBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      change (Result.ok (ControlFlow.done sums) = Result.ok (ControlFlow.done out)) at hrest
      exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some limb =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

private theorem body_cont_scalar_eq
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize)
    (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbody : InnerBody ops coeff iter sums scalar = .ok (.cont (iter', sums', scalar'))) :
    scalar' = scalar := by
  unfold InnerBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none => cases Result.ok.inj hrest
  | some limb =>
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨updated, _, hrest⟩ := bind_success _ _ _ hrest
      have hpair : (iter1, updated, scalar) = (iter', sums', scalar') :=
        ControlFlow.cont.inj (Result.ok.inj hrest)
      exact (congrArg (fun p => p.2.2) hpair).symm

private theorem body_success_starts_before_end
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) (iter iter' : Range)
    (sums sums' : Array U64 8#usize)
    (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbody : InnerBody ops coeff iter sums scalar = .ok (.cont (iter', sums', scalar'))) :
    iter.start.val < iter.end.val := by
  unfold InnerBody at hbody
  obtain ⟨⟨o, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      cases Result.ok.inj hrest
  | some limb =>
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter
      rw [hnext, WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · exact hlt
      · simp only [hlt, ↓reduceIte] at hspec
        rcases hspec with ⟨⟨hnone, _⟩, _⟩
        cases hnone

/-- A successful execution of the actual emitted limb loop preserves the
    four-cap envelope. At each continuation the emitted update is checked by
    the one-step theorem; unvisited limbs retain the three-cap bound. -/
theorem inner_loop_success_global_bound
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (iter : Range) (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (coeff : Array U32 8#usize)
    (hcoeff : ∀ i : Fin 8,
      (coeff.val[i.val]'(by simpa [coeff.property] using i.isLt)).val < 2147483647)
    (hbase4 : ∀ i : Fin 8,
      AspisR1FastDotsActualLimbPrefixStepV3.cell sums i ≤ 4 * cap)
    (hsuffix : ∀ i : Fin 8, iter.start.val ≤ i.val →
      AspisR1FastDotsActualLimbPrefixStepV3.cell sums i ≤ 3 * cap)
    (hscalar : scalar.val < 2147483647)
    (hloop : InnerLoop ops iter sums scalar coeff = .ok out) :
    ∀ i : Fin 8, AspisR1FastDotsActualLimbPrefixStepV3.cell out i ≤ 4 * cap := by
  induction hmeasure : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter sums scalar with
  | h m ih =>
      change Aeneas.Std.loop (innerStep ops coeff) (iter, sums, scalar) = .ok out at hloop
      rcases loop_success_cases (innerStep ops coeff) (iter, sums, scalar) out hloop with
        hdone | ⟨state', hcont, htail⟩
      · have hbody : InnerBody ops coeff iter sums scalar = .ok (.done out) := by
          simpa [innerStep] using hdone
        have hout := body_done_eq_sums ops coeff iter sums out scalar hbody
        subst out
        exact hbase4
      · rcases state' with ⟨iter', sums', scalar'⟩
        have hbody : InnerBody ops coeff iter sums scalar = .ok (.cont (iter', sums', scalar')) := by
          simpa [innerStep] using hcont
        obtain ⟨hstart, hend, hsuffix', hbase4'⟩ :=
          AspisR1FastDotsActualLimbPrefixStepV3.inner_body_success_preserves_prefix
            ops coeff iter iter' sums sums' scalar scalar' hcoeff hbase4 hsuffix hscalar hbody
        have hlt := body_success_starts_before_end ops coeff iter iter' sums sums' scalar scalar' hbody
        have hscalarEq := body_cont_scalar_eq ops coeff iter iter' sums sums' scalar scalar' hbody
        have hscalar' : scalar'.val < 2147483647 := by rw [hscalarEq]; exact hscalar
        have hdecrease : iter.end.val - iter'.start.val < m := by
          rw [hstart]
          omega
        have hmeasure' : iter'.end.val - iter'.start.val = iter.end.val - iter'.start.val := by
          rw [hend]
        have htail' : InnerLoop ops iter' sums' scalar' coeff = .ok out := by
          change Aeneas.Std.loop (innerStep ops coeff) (iter', sums', scalar') = .ok out
          exact htail
        exact ih _ hdecrease iter' sums' scalar' hbase4' hsuffix' hscalar' htail' hmeasure'


#print axioms inner_loop_success_global_bound

end AspisR1FastDotsActualInnerLoopBoundV1
