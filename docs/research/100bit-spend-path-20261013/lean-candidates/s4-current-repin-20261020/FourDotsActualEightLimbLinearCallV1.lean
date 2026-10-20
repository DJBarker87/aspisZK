import FourDotsActualInnerLoopLinearBoundV1
import FourDotsWideLimbCanonicalV1
import FourDotsActualEightLimbCallV1
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsActualEightLimbLinearCallV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev U64 := UScalar UScalarTy.U64
abbrev U32 := Std.U32
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev Range := core.ops.range.Range Usize
abbrev cap : Nat := AspisR1FastDotsActualInnerLoopLinearBoundV1.cap
abbrev InnerLoop := AspisR1FastDotsActualInnerLoopLinearBoundV1.InnerLoop

/-- One actual emitted eight-limb loop adds at most one product cap to any
    limb. The coefficient list is the real `toLimbs` output; only the source
    Wide coordinate-canonicality and scalar-canonicality contracts remain. -/
theorem current_wide_inner_loop_linear_bound
    (ops : Ops) (k : Nat) (hk : k ≤ 3)
    (x : Wide) (hx : AspisR1FastDotsWideLimbCanonical.CoordinateBound x)
    (iter : Range) (sums out : Array U64 8#usize)
    (scalar : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (coeff : Array U32 8#usize)
    (hcall : AspisR1EbyKPushWideToQ.toLimbs x = .ok coeff)
    (hinput : ∀ i : Fin 8,
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell sums i ≤ k * cap)
    (hscalar : scalar.val < 2147483647)
    (hloop : InnerLoop ops iter sums scalar coeff = .ok out) :
    ∀ i : Fin 8,
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell out i ≤ (k + 1) * cap := by
  have hcoeff := AspisR1FastDotsActualEightLimbCallV1.current_wide_coefficients_canonical
    x hx coeff (by simpa [AspisR1FastDotsActualEightLimbCallV1.withCurrentWideOps] using hcall)
  have hglobal : ∀ i : Fin 8,
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell sums i ≤ (k + 1) * cap := by
    intro i
    have hkcap : k * cap ≤ (k + 1) * cap :=
      Nat.mul_le_mul_right cap (Nat.le_succ k)
    exact le_trans (hinput i) hkcap
  have hsuffix : ∀ i : Fin 8, iter.start.val ≤ i.val →
      AspisR1FastDotsActualInnerLoopLinearBoundV1.cell sums i ≤ k * cap := by
    intro i _
    exact hinput i
  have hbound := AspisR1FastDotsActualInnerLoopLinearBoundV1.inner_loop_success_linear_bound
    ops k hk iter sums out scalar coeff
    hcoeff hglobal hsuffix hscalar hloop
  intro i
  have hcap : cap = 4611686009837453316 := by
    norm_num [cap, AspisR1FastDotsActualInnerLoopLinearBoundV1.cap]
  rw [hcap]
  exact hbound i

#print axioms current_wide_inner_loop_linear_bound

end AspisR1FastDotsActualEightLimbLinearCallV1
