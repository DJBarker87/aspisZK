import FourDotsActualLimbExactStepRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualLimbLoopExactRootV1

abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := Std.U32
abbrev Range := core.ops.range.Range Usize
abbrev InnerBody := AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0.body
abbrev InnerLoop := AspisR1FastDotsActualInnerLoopBoundV1.InnerLoop
abbrev cap : Nat := (2147483646)^2

def cell (a : Array U64 8#usize) (j : Fin 8) : Nat :=
  (a.val[j.val]'(by simpa [a.property] using j.isLt)).val

private theorem index_success_bound {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (x : α)
    (h : Array.index_usize a i = .ok x) : i.val < n.val := by
  have hlen : i.val < a.val.length := by
    by_contra hnot
    have hnone : a[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [a.property] using hlen

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

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

private def innerStep (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coeff : Array U32 8#usize) :
    (Range × Array U64 8#usize × AspisR1FastDotsCurrent.aspis_core.field.M31) →
      Result (ControlFlow (Range × Array U64 8#usize × AspisR1FastDotsCurrent.aspis_core.field.M31)
        (Array U64 8#usize)) :=
  fun s => InnerBody ops coeff s.1 s.2.1 s.2.2

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
  | none => cases Result.ok.inj hrest
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


abbrev coeffCell := AspisR1FastDotsActualLimbExactStepRootV1.coeffCell

private theorem body_done_exhausted
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coefficient : Array U32 8#usize) (iter : Range)
    (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hbody : InnerBody ops coefficient iter sums scalar = .ok (.done out)) :
    iter.end.val ≤ iter.start.val := by
  unfold InnerBody at hbody
  obtain ⟨⟨o,iter1⟩,hnext,hrest⟩ := bind_success _ _ _ hbody
  cases o with
  | none =>
      have hspec := Aeneas.Std.core.iter.range.IteratorRange.next_UScalar_spec
        (cloneInst := core.clone.CloneUsize)
        (partialOrdInst := core.cmp.PartialOrdUsize)
        (by intros; rfl) (by intros; rfl) iter
      rw [hnext,WP.spec_ok] at hspec
      by_cases hlt : iter.start.val < iter.end.val
      · simp only [hlt,↓reduceIte] at hspec
        rcases hspec with ⟨⟨hopt,_⟩,_⟩
        cases hopt
      · omega
  | some limb =>
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨_,_,hrest⟩ := bind_success _ _ _ hrest
      cases Result.ok.inj hrest

/-- The visited-prefix equation is preserved by the complete actual loop.
The result tracks exact natural sums, not merely their range. -/
theorem actual_inner_loop_success_exact_invariant
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coefficient : Array U32 8#usize) (initial : Array U64 8#usize)
    (hcoeff : ∀ j : Fin 8, coeffCell coefficient j < 2147483647)
    (hbase : ∀ j : Fin 8, cell initial j ≤ 3 * cap)
    (iter : Range) (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hscalar : scalar.val < 2147483647)
    (hend : iter.end.val = 8)
    (hprefix : ∀ j : Fin 8, cell sums j = cell initial j +
      if j.val < iter.start.val then coeffCell coefficient j * scalar.val else 0)
    (hloop : InnerLoop ops iter sums scalar coefficient = .ok out) :
    ∀ j : Fin 8, cell out j = cell initial j + coeffCell coefficient j * scalar.val := by
  induction hm : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter sums scalar with
  | h m ih =>
      change Aeneas.Std.loop (innerStep ops coefficient) (iter,sums,scalar) = .ok out at hloop
      rcases loop_success_cases (innerStep ops coefficient) (iter,sums,scalar) out hloop with
        hdone | ⟨state',hcont,htail⟩
      · have hb : InnerBody ops coefficient iter sums scalar = .ok (.done out) := by
          simpa only [innerStep] using hdone
        have hout := body_done_eq_sums ops coefficient iter sums out scalar hb
        have hexhaust := body_done_exhausted ops coefficient iter sums out scalar hb
        intro j
        have hj : j.val < iter.start.val := by omega
        rw [hout,hprefix j,if_pos hj]
      · rcases state' with ⟨iter',sums',scalar'⟩
        have hb : InnerBody ops coefficient iter sums scalar =
            .ok (.cont (iter',sums',scalar')) := by simpa only [innerStep] using hcont
        have hcurrent : ∀ j : Fin 8, j.val = iter.start.val → cell sums j ≤ 3 * cap := by
          intro j hj
          have hn : ¬j.val < iter.start.val := by omega
          rw [hprefix j,if_neg hn,Nat.add_zero]
          exact hbase j
        obtain ⟨hadvance,hendEq,hcells⟩ :=
          AspisR1FastDotsActualLimbExactStepRootV1.actual_limb_body_success_exact_step
            ops coefficient iter iter' sums sums' scalar scalar' hcoeff hcurrent hscalar hb
        have hscalarEq := body_cont_scalar_eq ops coefficient iter iter' sums sums' scalar scalar' hb
        have hlt := body_success_starts_before_end ops coefficient iter iter' sums sums' scalar scalar' hb
        have hdecrease : iter.end.val - iter'.start.val < m := by rw [hadvance]; omega
        have hscalar' : scalar'.val < 2147483647 := by rw [hscalarEq]; exact hscalar
        have hend' : iter'.end.val = 8 := by rw [hendEq,hend]
        have hprefix' : ∀ j : Fin 8, cell sums' j = cell initial j +
            if j.val < iter'.start.val then coeffCell coefficient j * scalar'.val else 0 := by
          intro j
          rw [hscalarEq,hcells j,hprefix j]
          by_cases heq : j.val = iter.start.val
          · have hold : ¬j.val < iter.start.val := by omega
            have hnew : j.val < iter'.start.val := by omega
            rw [if_pos heq,if_neg hold,if_pos hnew,Nat.add_zero]
          · have hequiv : (j.val < iter.start.val) = (j.val < iter'.start.val) := by
              apply propext
              constructor <;> intro hh <;> omega
            rw [if_neg heq,hequiv]
        have htail' : InnerLoop ops iter' sums' scalar' coefficient = .ok out := by
          change Aeneas.Std.loop (innerStep ops coefficient) (iter',sums',scalar') = .ok out
          exact htail
        have hm' : iter'.end.val - iter'.start.val = iter.end.val - iter'.start.val := by rw [hendEq]
        have hout := ih _ hdecrease iter' sums' scalar' hscalar' hend' hprefix' htail' hm'
        simpa only [hscalarEq] using hout

/-- One successful actual eight-limb loop adds exactly the scalar product to
each original accumulator coordinate. No output-value equation is assumed. -/
theorem actual_eight_limb_loop_success_exact
    (ops : AspisR1FastDotsCurrent.FourDotsOps)
    (coefficient : Array U32 8#usize) (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hcoeff : ∀ j : Fin 8, coeffCell coefficient j < 2147483647)
    (hbase : ∀ j : Fin 8, cell sums j ≤ 3 * cap)
    (hscalar : scalar.val < 2147483647)
    (hloop : InnerLoop ops {start := 0#usize, «end» := 8#usize} sums scalar coefficient = .ok out) :
    ∀ j : Fin 8, cell out j = cell sums j + coeffCell coefficient j * scalar.val := by
  apply actual_inner_loop_success_exact_invariant ops coefficient sums hcoeff hbase
    {start := 0#usize, «end» := 8#usize} sums out scalar hscalar (by decide) _ hloop
  intro j
  simp only [show (0#usize).val = 0 from rfl,Nat.not_lt_zero,if_false,Nat.add_zero]

#print axioms actual_inner_loop_success_exact_invariant
#print axioms actual_eight_limb_loop_success_exact
end AspisR1FastDotsActualLimbLoopExactRootV1
