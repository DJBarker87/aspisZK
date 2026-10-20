import FourDotsWideLimbCanonicalV1
import FourDotsActualLimbArithmeticStepV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1FastDotsWideToActualLimbStep

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev U32 := Std.U32
abbrev U64 := Std.U64
abbrev Range := core.ops.range.Range Usize
abbrev InnerBody :=
  AspisR1FastDotsCurrent.fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut_loop0_loop0_loop0.body

def withActualWideToLimbs (ops : Ops) : Ops :=
  { ops with wideToLimbs := AspisR1EbyKPushWideToQ.toLimbs }

theorem selected_coefficient_layout
    (ops : Ops) (x : Wide) :
    (withActualWideToLimbs ops).wideToLimbs x =
      .ok (AspisR1FastDotsWideLimbCanonical.limbArray x) := by
  exact AspisR1FastDotsWideLimbCanonical.toLimbs_actual_value x

theorem wideToLimbs_call_fixes_coefficients
    (ops : Ops) (x : Wide) (coefficients : Array U32 8#usize)
    (hcall : (withActualWideToLimbs ops).wideToLimbs x = .ok coefficients) :
    coefficients = AspisR1FastDotsWideLimbCanonical.limbArray x := by
  exact Result.ok.inj
    (hcall.symm.trans (selected_coefficient_layout ops x))

/-- The actual generated inner limb body, supplied the array returned by the
    accepted `wideToLimbs` binding, performs the canonical widened multiply
    and checked addition. Only the scalar and prior batch-prefix invariants
    remain caller inputs. -/
theorem inner_body_success_wide_coefficients
    (ops : Ops) (x : Wide)
    (hx : AspisR1FastDotsWideLimbCanonical.CoordinateBound x)
    (coefficients : Array U32 8#usize)
    (hcall : (withActualWideToLimbs ops).wideToLimbs x = .ok coefficients)
    (iter iter' : Range) (sums sums' : Array U64 8#usize)
    (scalar scalar' : AspisR1FastDotsCurrent.aspis_core.field.M31)
    (hprefix : ∀ i : Fin 8,
      (sums.val[i.val]'(by simpa [sums.property] using i.isLt)).val ≤
        3 * AspisR1FastDotsActualLimbArithmeticStep.cap)
    (hscalar : scalar.val < 2147483647)
    (hbody : InnerBody (withActualWideToLimbs ops) coefficients iter sums scalar =
        .ok (.cont (iter', sums', scalar'))) :
    ∃ limb : Usize, ∃ coeff : U32, ∃ oldSum : U64,
      ∃ product : U64, ∃ newSum : U64,
        Array.index_usize (AspisR1FastDotsWideLimbCanonical.limbArray x) limb = .ok coeff ∧
        Array.index_usize sums limb = .ok oldSum ∧
        UScalar.mul (core.convert.num.FromU64U32.from coeff)
          (core.convert.num.FromU64U32.from scalar) = .ok product ∧
        UScalar.add oldSum product = .ok newSum ∧
        product.val = coeff.val * scalar.val ∧
        product.val ≤ AspisR1FastDotsActualLimbArithmeticStep.cap ∧
        newSum.val = oldSum.val + product.val := by
  have hcoeffeq := wideToLimbs_call_fixes_coefficients ops x coefficients hcall
  subst coefficients
  exact AspisR1FastDotsActualLimbArithmeticStep.inner_body_success_arithmetic
    (withActualWideToLimbs ops)
    (AspisR1FastDotsWideLimbCanonical.limbArray x)
    iter iter' sums sums' scalar scalar'
    (AspisR1FastDotsWideLimbCanonical.all_emitted_limb_entries_canonical x hx)
    hprefix hscalar hbody

#print axioms selected_coefficient_layout
#print axioms inner_body_success_wide_coefficients
#print axioms wideToLimbs_call_fixes_coefficients

end AspisR1FastDotsWideToActualLimbStep
