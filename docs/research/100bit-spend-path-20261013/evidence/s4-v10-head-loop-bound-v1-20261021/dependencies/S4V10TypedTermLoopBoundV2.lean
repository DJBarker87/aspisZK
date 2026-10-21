import S4V10TypedInnerBodyBoundV1
import NewTermBodyLinearBoundV1

open Aeneas Aeneas.Std Result ControlFlow
noncomputable section
namespace AspisR1FastDotsV10TypedTermLoopBoundV1

open AspisR1FastDotsV10TypedInnerBodyOpsV1
abbrev CurrentOps := AspisR1FastDotsCurrent.FourDotsOps
abbrev Usize := Aeneas.Std.Usize
abbrev U64 := Aeneas.Std.U64
abbrev Range := Aeneas.Std.core.ops.range.Range Usize
abbrev CurrentWide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact
abbrev cap := AspisR1FastDotsNewTermBodyLinearBoundV1.cap
abbrev cell := AspisR1FastDotsNewTermBodyLinearBoundV1.cell

def v10TermLoop
    (ops : BodyOps) (iter : Range)
    (q : Aeneas.Std.Array Aeneas.Std.U8 608#usize)
    (g : Aeneas.Std.Array V10Wide 29#usize) (slot : Usize)
    (sums : Aeneas.Std.Array U64 8#usize) : Result (Aeneas.Std.Array U64 8#usize) :=
  Aeneas.Std.loop
    (fun st : Range × Aeneas.Std.Array U64 8#usize =>
      v10TermBody ops q g slot st.1 st.2)
    (iter, sums)

/-- The V10 loop shell uses the exact V10 term body. Replacing that body by its
    checked mapped Current body leaves the same Aeneas loop and state. -/
theorem v10TermLoop_eq_fixedLoopV2
    (ops : CurrentOps) (q : Aeneas.Std.Array Aeneas.Std.U8 608#usize)
    (g : Aeneas.Std.Array V10Wide 29#usize) (slot : Usize)
    (iter : Range) (sums : Aeneas.Std.Array U64 8#usize) :
    v10TermLoop (adaptOps ops) iter q g slot sums =
      AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0_loop0
        ops iter q (mapWideArray g) slot sums := by
  change Aeneas.Std.loop
      (fun st : Range × Aeneas.Std.Array U64 8#usize =>
        v10TermBody (adaptOps ops) q g slot st.1 st.2) (iter, sums) =
    Aeneas.Std.loop
      (fun st : Range × Aeneas.Std.Array U64 8#usize =>
        AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0_loop0.body ops q
          (mapWideArray g) slot st.1 st.2) (iter, sums)
  apply congrArg (fun body => Aeneas.Std.loop body (iter, sums))
  funext st
  exact v10TermBody_eq_fixedBody ops q g slot st.1 st.2

/-- A successful V10 term-loop result therefore inherits the retained v6
    source-derived per-term envelope, on the same mapped `g` and sums. -/
theorem v10_term_loop_success_linear_boundV2
    (ops : CurrentOps) (k : Nat) (q : Aeneas.Std.Array Aeneas.Std.U8 608#usize)
    (g : Aeneas.Std.Array V10Wide 29#usize) (slot : Usize)
    (iter : Range) (sums out : Aeneas.Std.Array U64 8#usize) (d : Nat)
    (hparser : ops.m31FromBytes = AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes)
    (hwide : ops.wideToLimbs = AspisR1EbyKPushWideToQ.toLimbs)
    (hcoord : ∀ i : Fin 29,
      AspisR1FastDotsWideLimbCanonical.CoordinateBound
        ((mapWideArray g).val[i.val]'(by simpa [(mapWideArray g).property] using i.isLt)))
    (hinput : ∀ i : Fin 8, cell sums i ≤ k * cap)
    (hsize : iter.end.val - iter.start.val ≤ d)
    (hbudget : k + d ≤ 4)
    (hloop : v10TermLoop (adaptOps ops) iter q g slot sums = .ok out) :
    ∀ i : Fin 8, cell out i ≤ (k + d) * cap := by
  have hfixed :
      AspisR1FastDotsCurrent.fast_dots.four_dots_one_loop0_loop0
        ops iter q (mapWideArray g) slot sums = .ok out :=
    (v10TermLoop_eq_fixedLoopV2 ops q g slot iter sums).symm.trans hloop
  exact AspisR1FastDotsNewTermBodyLinearBoundV1.new_term_loop_success_linear_bound
    ops k q (mapWideArray g) slot iter sums out d hparser hwide hcoord hinput
    hsize hbudget hfixed

#print axioms v10TermLoop_eq_fixedLoopV2
#print axioms v10_term_loop_success_linear_boundV2
end AspisR1FastDotsV10TypedTermLoopBoundV1
