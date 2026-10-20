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
  obtain ⟨term, bytes, wide, coeff, scalar, _sums1, _sums2, _sums3, _sums4,
      _sums5, _sums6, _sums7, _sums8, hread, hcoeffOps, hparserOps,
      _h0, _h1, _h2, _h3, _h4, _h5, _h6, _h7, _hfinal, hloop⟩ :=
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

#print axioms new_term_body_success_linear_bound

end AspisR1FastDotsNewTermBodyLinearBoundV1
