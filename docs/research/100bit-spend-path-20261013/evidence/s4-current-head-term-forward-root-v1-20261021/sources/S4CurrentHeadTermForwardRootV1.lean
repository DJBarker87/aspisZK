import S4HeadTermForwardRootV1
import FourDotsActualEightLimbCallV1
import AspisR1DecodeKFullV10ParserCanonicality
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1FastDotsCurrentHeadTermForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops M31)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide TermBody ReadWitness)
open AspisR1FastDotsActualInnerLoopLinearBoundV1 (Range cap cell)

def install (ops : Ops) : Ops :=
  {ops with
    wideLimbCount := .ok 8#usize
    wideToLimbs := AspisR1EbyKPushWideToQ.toLimbs
    m31FromBytes := AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes}

theorem current_term_body_forward
    (base : Ops) (k : Nat) (hk : k≤3)
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (slot term : Usize) (iter iter' : Range) (sums : Array Std.U64 8#usize)
    (r : ReadWitness a g slot term) (scalar : M31)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some term,iter'))
    (hp : AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes r.copied = .ok (some scalar))
    (hx : AspisR1FastDotsWideLimbCanonical.CoordinateBound r.coefficient)
    (hinput : ∀ j : Fin 8, cell sums j ≤ k*cap) :
    ∃ out : Array Std.U64 8#usize,
      TermBody (install base) a g slot iter sums = .ok (.cont (iter',out)) ∧
      (∀ j : Fin 8, cell out j ≤ (k+1)*cap) := by
  have hw := AspisR1FastDotsWideLimbCanonical.toLimbs_actual_value r.coefficient
  have hcoeff := AspisR1FastDotsActualEightLimbCallV1.current_wide_coefficients_canonical
    r.coefficient hx (AspisR1FastDotsWideLimbCanonical.limbArray r.coefficient) hw
  have hscalar : scalar.val<2147483647 := by
    have hc := AspisR1DecodeKFullV10ParserCanonicality.m31_from_le_bytes_success_canonical
      r.copied scalar hp
    simpa [AspisR1DecodeKFullV10.aspis_core.field.P] using hc
  exact AspisR1FastDotsHeadTermForwardRootV1.term_body_forward (install base) k hk
    a g slot term iter iter' sums r scalar
    (AspisR1FastDotsWideLimbCanonical.limbArray r.coefficient) hn hp hw rfl hcoeff hscalar hinput

#print axioms current_term_body_forward
end AspisR1FastDotsCurrentHeadTermForwardRootV1
