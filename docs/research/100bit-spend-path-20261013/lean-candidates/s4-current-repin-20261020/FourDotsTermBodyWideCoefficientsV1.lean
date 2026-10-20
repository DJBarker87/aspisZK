import FourDotsActualEightLimbCallV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsTermBodyWideCoefficientsV1

abbrev Ops := AspisR1FastDotsActualEightLimbCallV1.Ops
abbrev Usize := Std.Usize
abbrev U8 := Std.U8
abbrev U64 := UScalar UScalarTy.U64
abbrev Wide := AspisR1FastDotsActualEightLimbCallV1.Wide
abbrev Range := core.ops.range.Range Usize
abbrev Body :=
  AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0.body

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- A successful generated term-body call actually reads one `WideExact`
    coefficient from its 29-entry input and runs the current `to_limbs`
    implementation. If that selected input has canonical M31 coordinates,
    the exact coefficient array consumed by the limb loop is canonical. The
    byte-slice and scalar parser calls remain part of the same successful body;
    no independent success for `wideToLimbs` is assumed. -/
theorem body_success_selected_coefficient_canonical
    (ops : Ops) (a : Array U8 608#usize) (a1 : Array Wide 29#usize)
    (slot : Usize) (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (hcoords : ∀ term x, Array.index_usize a1 term = .ok x →
      AspisR1FastDotsWideLimbCanonical.CoordinateBound x)
    (hbody : Body (AspisR1FastDotsActualEightLimbCallV1.withCurrentWideOps ops)
      a a1 slot iter sums = .ok (.cont (iter', sums'))) :
    ∃ term x coeff,
      Array.index_usize a1 term = .ok x ∧
      AspisR1FastDotsWideLimbCanonical.CoordinateBound x ∧
      AspisR1EbyKPushWideToQ.toLimbs x = .ok coeff ∧
      (∀ i : Fin 8,
        (coeff.val[i.val]'(by simpa [coeff.property] using i.isLt)).val < 2147483647) := by
  unfold Body at hbody
  obtain ⟨⟨term?, iter1⟩, hnext, hrest⟩ := bind_success _ _ _ hbody
  cases term? with
  | none =>
      have hflow : ControlFlow.done sums = ControlFlow.cont (iter', sums') :=
        Result.ok.inj hrest
      cases hflow
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
      obtain ⟨x, hread, hrest⟩ := bind_success _ _ _ hrest
      obtain ⟨coeff, hcall, _⟩ := bind_success _ _ _ hrest
      have hcall' : AspisR1EbyKPushWideToQ.toLimbs x = .ok coeff := by
        change (AspisR1FastDotsActualEightLimbCallV1.withCurrentWideOps ops).wideToLimbs x = .ok coeff at hcall
        simpa [AspisR1FastDotsActualEightLimbCallV1.withCurrentWideOps,
          AspisR1FastDotsActualEightLimbCallV1.withCurrentLimbCount8] using hcall
      have hx := hcoords term x hread
      have hcoeff := AspisR1FastDotsActualEightLimbCallV1.current_wide_coefficients_canonical
        x hx coeff hcall'
      exact ⟨term, x, coeff, hread, hx, hcall', hcoeff⟩

#print axioms body_success_selected_coefficient_canonical

end AspisR1FastDotsTermBodyWideCoefficientsV1
