import S4V10LiteralHelperSourceCutV1
import S4V10LiteralOuterTransferRootV1

open Aeneas Aeneas.Std Result
namespace AspisR1S4V10CountSlotIrrelevanceV1

open AspisR1FastDotsV10LiteralHelperSourceCutV1
open AspisR1FastDotsV10LiteralOuterTransferRootV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev Usize := Aeneas.Std.Usize

def replaceWideLimbCount (ops : Ops) (count : Result Usize) : Ops :=
  { ops with wideLimbCount := count }

theorem literal_helper_independent_wide_limb_count
    (ops : Ops) (count : Result Usize) (q : Array Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) :
    literalV10Helper (replaceWideLimbCount ops count) q g slot =
      literalV10Helper ops q g slot := by
  cases ops
  rfl

theorem literal_outer_independent_wide_limb_count
    (ops : Ops) (count : Result Usize) (q : Slice Std.U8)
    (g : Array V10Wide 29#usize) :
    literalV10Outer (replaceWideLimbCount ops count) q g =
      literalV10Outer ops q g := by
  cases ops
  rfl

#print axioms literal_helper_independent_wide_limb_count
#print axioms literal_outer_independent_wide_limb_count

end AspisR1S4V10CountSlotIrrelevanceV1
