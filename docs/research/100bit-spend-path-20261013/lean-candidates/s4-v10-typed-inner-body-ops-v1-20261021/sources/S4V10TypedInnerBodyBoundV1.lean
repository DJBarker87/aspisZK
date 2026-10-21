import S4V10TypedInnerBodyOpsV1
import NewTermBodyLinearBoundV1

open Aeneas Aeneas.Std Result ControlFlow
noncomputable section
namespace AspisR1FastDotsV10TypedInnerBodyBoundV1

open AspisR1FastDotsV10TypedInnerBodyOpsV1
abbrev CurrentOps := AspisR1FastDotsCurrent.FourDotsOps
abbrev Usize := Aeneas.Std.Usize
abbrev U64 := Aeneas.Std.U64
abbrev Range := Aeneas.Std.core.ops.range.Range Usize
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev cap := AspisR1FastDotsNewTermBodyLinearBoundV1.cap
abbrev cell := AspisR1FastDotsNewTermBodyLinearBoundV1.cell

/-- A successful V10 transparent-carrier term body step is the same successful
    step consumed by the retained v6 source-derived linear bound theorem. The
    input `g` is transported pointwise by `mapWideArray`; the output sums are
    shared literally. -/
theorem v10_term_body_success_linear_bound
    (ops : CurrentOps) (k : Nat) (hk : k ≤ 3)
    (q : Aeneas.Std.Array Aeneas.Std.U8 608#usize)
    (g : Aeneas.Std.Array V10Wide 29#usize) (slot : Usize)
    (iter iter' : Range) (sums sums' : Aeneas.Std.Array U64 8#usize)
    (hparser : ops.m31FromBytes = AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes)
    (hwide : ops.wideToLimbs = AspisR1EbyKPushWideToQ.toLimbs)
    (hcoords : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        ((mapWideArray g).val[i.val]'(by simpa [(mapWideArray g).property] using i.isLt)))
    (hinput : ∀ i : Fin 8, cell sums i ≤ k * cap)
    (hbody : v10TermBody (adaptOps ops) q g slot iter sums =
      .ok (.cont (iter', sums'))) :
    ∀ i : Fin 8, cell sums' i ≤ (k + 1) * cap := by
  have hfixed :
      AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0_loop0.body
        ops q (mapWideArray g) slot iter sums = .ok (.cont (iter', sums')) :=
    (v10TermBody_eq_fixedBody ops q g slot iter sums).symm.trans hbody
  exact AspisR1FastDotsNewTermBodyLinearBoundV1.new_term_body_success_linear_bound
    ops k hk q (mapWideArray g) slot iter iter' sums sums' hparser hwide
    hcoords hinput hfixed

#print axioms v10_term_body_success_linear_bound
end AspisR1FastDotsV10TypedInnerBodyBoundV1
