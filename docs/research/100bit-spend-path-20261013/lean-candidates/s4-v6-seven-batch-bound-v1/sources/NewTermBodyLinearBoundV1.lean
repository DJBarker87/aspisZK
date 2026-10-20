import FixedInnerBodyStepBridgeV1
import FourDotsActualInnerLoopLinearBoundV1
import FourDotsActualEightLimbCallV1
import AspisR1DecodeKFullV10ParserCanonicality
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsNewTermBodyLinearBoundV1

abbrev Ops := AspisR1FastDotsFixedInnerBodyStepBridgeV1.Ops
abbrev Usize := Std.Usize
abbrev U32 := Std.U32
abbrev U64 := UScalar UScalarTy.U64
abbrev M31 := AspisR1FastDotsCurrent.aspis_core.field.M31
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Range := core.ops.range.Range Usize
abbrev cap := AspisR1FastDotsActualInnerLoopLinearBoundV1.cap
abbrev cell := AspisR1FastDotsActualInnerLoopLinearBoundV1.cell
abbrev NewTermLoop := AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0_loop0

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Success of the exact eight-segment term body bounds its output using the
    retained emitted inner-loop proof. The only data premises are the source
    coordinate bounds for `g` and the prior sums envelope; scalar and limb
    bounds are recovered from the successful parser/toLimbs calls in the body. -/
theorem new_term_body_success_linear_bound
    (ops : Ops) (k : Nat) (hk : k ≤ 3)
    (q : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hparser : ops.m31FromBytes = AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes)
    (hwide : ops.wideToLimbs = AspisR1EbyKPushWideToQ.toLimbs)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    (hinput : ∀ i : Fin 8, cell sums i ≤ k * cap)
    (hbody : AspisR1FastDotsFixedInnerBodyStepBridgeV1.NewTermBody ops q g slot iter sums =
      .ok (.cont (iter', sums'))) :
    ∀ i : Fin 8, cell sums' i ≤ (k + 1) * cap := by
  obtain ⟨_iter1, term, bytes, wide, coeff, scalar, _sums1, _sums2, _sums3, _sums4,
      _sums5, _sums6, _sums7, _sums8, hread, hcoeffOps, hparserOps,
      _hnextBody, _hiterBody, _h0, _h1, _h2, _h3, _h4, _h5, _h6, _h7, _hfinal, hloop⟩ :=
    AspisR1FastDotsFixedInnerBodyStepBridgeV1.new_term_body_success_supplies_old_inner_loop
      ops q g slot iter iter' sums sums' hbody
  have htermBound : term.val < 29 := by
    have hidx : term.val < g.val.length := by
      by_contra hnot
      have hnone : g[term]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
      unfold Array.index_usize at hread
      rw [hnone] at hread
      cases hread
    simpa [g.property] using hidx
  have hreadSpec := WP.spec_imp_exists
    (Array.index_usize_spec g term (by simpa [g.property] using htermBound))
  obtain ⟨value, hreadSpec, hvalue⟩ := hreadSpec
  have hvalueEq : value = wide := Result.ok.inj (hreadSpec.symm.trans hread)
  have hget : wide = g.val[term.val]'(by simpa [g.property] using htermBound) :=
    hvalueEq.symm.trans hvalue
  have hwideCanon : AspisR1FastDotsWideLimbCanonical.CoordinateBound wide := by
    rw [hget]
    exact hcoords ⟨term.val, htermBound⟩
  have hparserActual : AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes bytes =
      .ok (some scalar) := by
    simpa only [hparser] using hparserOps
  have hscalar : scalar.val < 2147483647 := by
    simpa [AspisR1DecodeKFullV10.aspis_core.field.P] using
      AspisR1DecodeKFullV10ParserCanonicality.m31_from_le_bytes_success_canonical
        bytes scalar hparserActual
  have hcoeffActual : AspisR1EbyKPushWideToQ.toLimbs wide = .ok coeff := by
    simpa only [hwide] using hcoeffOps
  have hcoeff := AspisR1FastDotsActualEightLimbCallV1.current_wide_coefficients_canonical
    wide hwideCanon coeff hcoeffActual
  have hbase : ∀ i : Fin 8, cell sums i ≤ (k + 1) * cap := by
    intro i
    exact le_trans (hinput i) (Nat.mul_le_mul_right cap (Nat.le_succ k))
  have hsuffix : ∀ i : Fin 8,
      AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_zero.start.val ≤ i.val →
      cell sums i ≤ k * cap := by
    intro i _
    exact hinput i
  exact AspisR1FastDotsActualInnerLoopLinearBoundV1.inner_loop_success_linear_bound
    ops k hk AspisR1FastDotsFixedInnerBodyStepBridgeV1.limb_range_zero sums sums' scalar coeff
    hcoeff hbase hsuffix hscalar hloop

theorem new_term_body_cont_progress
    (ops : Ops) (q : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hbody : AspisR1FastDotsFixedInnerBodyStepBridgeV1.NewTermBody ops q g slot iter sums =
      .ok (.cont (iter', sums'))) :
    iter.start.val < iter.end.val ∧
      iter'.start.val = iter.start.val + 1 ∧ iter'.end = iter.end := by
  obtain ⟨iter1, _term, _bytes, _wide, _coeff, _scalar, _sums1, _sums2,
      _sums3, _sums4, _sums5, _sums6, _sums7, _sums8, _hread, _hcoeff,
      _hparser, hnext, hiter, _h0, _h1, _h2, _h3, _h4, _h5, _h6, _h7,
      _hfinal, _hloop⟩ :=
    AspisR1FastDotsFixedInnerBodyStepBridgeV1.new_term_body_success_supplies_old_inner_loop
      ops q g slot iter iter' sums sums' hbody
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
    rcases hspec with ⟨⟨_hopt, hadvance⟩, hend⟩
    exact ⟨hlt, by simpa [hiter] using hadvance, by simpa [hiter] using hend⟩
  · simp only [hlt, ↓reduceIte] at hspec
    rcases hspec with ⟨⟨hnone, _hadvance⟩, _hend⟩
    cases hnone

private def newTermStep (ops : Ops) (q : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) :
    (Range × Array U64 8#usize) → Result (ControlFlow (Range × Array U64 8#usize)
      (Array U64 8#usize)) :=
  fun st => AspisR1FastDotsFixedInnerBodyStepBridgeV1.NewTermBody ops q g slot st.1 st.2

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
          have heq : result = out := Result.ok.inj h
          subst result
          exact Or.inl rfl
      | cont stateNext =>
          simp only [hs, bind_tc_ok] at h
          exact Or.inr ⟨stateNext, rfl, h⟩

private theorem new_term_body_done_identity
    (ops : Ops) (q : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot : Usize) (iter : Range) (sums out : Array U64 8#usize)
    (hbody : AspisR1FastDotsFixedInnerBodyStepBridgeV1.NewTermBody ops q g slot iter sums =
      .ok (.done out)) : out = sums := by
  unfold AspisR1FastDotsFixedInnerBodyStepBridgeV1.NewTermBody at hbody
  obtain ⟨⟨o, _iter1⟩, _hnext, hrest⟩ :=
    bind_success _ _ _ hbody
  cases o with
  | none => exact (ControlFlow.done.inj (Result.ok.inj hrest)).symm
  | some _ =>
      repeat' (first |
        obtain ⟨_, _, hrest⟩ := bind_success _ _ _ hrest)
      cases Result.ok.inj hrest

/-- The actual v6 term loop inherits the old per-term envelope: every
    successful body step is bounded by the source-derived v6 term theorem,
    and the emitted RangeIter supplies the decreasing measure. -/
theorem new_term_loop_success_linear_bound
    (ops : Ops) (k : Nat) (q : Array Std.U8 608#usize)
    (g : Array Wide 29#usize) (slot : Usize) (iter : Range)
    (sums out : Array U64 8#usize) (d : Nat)
    (hparser : ops.m31FromBytes = AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes)
    (hwide : ops.wideToLimbs = AspisR1EbyKPushWideToQ.toLimbs)
    (hcoord : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        (g.val[i.val]'(by simpa [g.property] using i.isLt)))
    (hinput : ∀ i : Fin 8, cell sums i ≤ k * cap)
    (hsize : iter.end.val - iter.start.val ≤ d)
    (hbudget : k + d ≤ 4)
    (hloop : NewTermLoop ops iter q g slot sums = .ok out) :
    ∀ i : Fin 8, cell out i ≤ (k + d) * cap := by
  induction hm : iter.end.val - iter.start.val using Nat.strong_induction_on
      generalizing iter sums k d with
  | h m ih =>
      change Aeneas.Std.loop (newTermStep ops q g slot) (iter, sums) = .ok out at hloop
      rcases loop_success_cases _ _ _ hloop with hdone | ⟨st', hcont, htail⟩
      · have hbody : AspisR1FastDotsFixedInnerBodyStepBridgeV1.NewTermBody ops q g slot iter sums =
            .ok (.done out) := by simpa [newTermStep] using hdone
        have hout := new_term_body_done_identity ops q g slot iter sums out hbody
        subst out
        intro i
        have hkd : k ≤ k + d := by omega
        exact le_trans (hinput i) (Nat.mul_le_mul_right cap hkd)
      · rcases st' with ⟨iter', sums'⟩
        have hbody : AspisR1FastDotsFixedInnerBodyStepBridgeV1.NewTermBody ops q g slot iter sums =
            .ok (.cont (iter', sums')) := by simpa [newTermStep] using hcont
        obtain ⟨hlt, hadvance, hend⟩ := new_term_body_cont_progress
          ops q g slot iter iter' sums sums' hbody
        have hdist : iter'.end.val - iter'.start.val + 1 =
            iter.end.val - iter.start.val := by rw [hend, hadvance]; omega
        have hdist' : iter'.end.val - iter'.start.val =
            iter.end.val - iter.start.val - 1 := by omega
        have hdpos : 0 < iter.end.val - iter.start.val := by omega
        have hk3 : k ≤ 3 := by omega
        have hsum' : ∀ i : Fin 8, cell sums' i ≤ (k + 1) * cap :=
          new_term_body_success_linear_bound ops k hk3 q g slot iter iter' sums sums'
            hparser hwide hcoord hinput hbody
        have hsize' : iter'.end.val - iter'.start.val ≤ d - 1 := by omega
        have hbudget' : (k + 1) + (d - 1) ≤ 4 := by omega
        have htail' := ih (iter.end.val - iter.start.val - 1) (by omega)
          (k + 1) iter' sums' (d - 1) hsum' hsize' hbudget' htail hdist'
        intro i
        have hsameMeasure : k + d = (k + 1) + (d - 1) := by omega
        rw [hsameMeasure]
        exact htail' i

#print axioms new_term_body_success_linear_bound
#print axioms new_term_body_cont_progress
#print axioms new_term_loop_success_linear_bound

end AspisR1FastDotsNewTermBodyLinearBoundV1
