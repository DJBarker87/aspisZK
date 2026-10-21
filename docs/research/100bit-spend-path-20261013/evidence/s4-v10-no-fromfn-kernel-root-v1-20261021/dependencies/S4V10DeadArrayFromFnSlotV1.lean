import S4V10LiteralOuterTransferRootV1
import S4V10HeadLoopBoundV1
import S4V10TypedInnerBodyOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1FastDotsV10DeadArrayFromFnSlotV1

open AspisR1FastDotsV10LiteralHelperSourceCutV1
open AspisR1FastDotsV10HeadLoopBoundV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev Usize := Aeneas.Std.Usize
abbrev U64 := Aeneas.Std.U64
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact

/-- Replace only the array constructor callback in an operation record. -/
def withArrayFromFn (ops replacement : Ops) : Ops :=
  { ops with arrayFromFn := replacement.arrayFromFn }

/-- The actual V10 term body sees only the two explicitly projected operation
slots. Changing `arrayFromFn` therefore does not affect a term step. -/
theorem adaptOps_arrayFromFn_irrelevant (ops replacement : Ops) :
    adaptOps (withArrayFromFn ops replacement) = adaptOps ops := rfl

theorem v10HeadBody_arrayFromFn_irrelevant
    (ops replacement : Ops) (q : Array Aeneas.Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize)
    (iter : StepBy) (limbs : Array U64 8#usize) :
    v10HeadBody (withArrayFromFn ops replacement) q g slot iter limbs =
      v10HeadBody ops q g slot iter limbs := by
  unfold v10HeadBody
  rw [adaptOps_arrayFromFn_irrelevant]

theorem v10HeadLoop_arrayFromFn_irrelevant
    (ops replacement : Ops) (iter : StepBy)
    (q : Array Aeneas.Std.U8 608#usize) (g : Array V10Wide 29#usize)
    (slot : Usize) (limbs : Array U64 8#usize) :
    v10HeadLoop (withArrayFromFn ops replacement) iter q g slot limbs =
      v10HeadLoop ops iter q g slot limbs := by
  change Aeneas.Std.loop
      (fun st : StepBy × Array U64 8#usize =>
        v10HeadBody (withArrayFromFn ops replacement) q g slot st.1 st.2)
      (iter, limbs) =
    Aeneas.Std.loop
      (fun st : StepBy × Array U64 8#usize => v10HeadBody ops q g slot st.1 st.2)
      (iter, limbs)
  apply congrArg (fun body => Aeneas.Std.loop body (iter, limbs))
  funext st
  exact v10HeadBody_arrayFromFn_irrelevant ops replacement q g slot st.1 st.2

theorem literalV10Helper_arrayFromFn_irrelevant
    (ops replacement : Ops) (q : Array Aeneas.Std.U8 608#usize)
    (g : Array V10Wide 29#usize) (slot : Usize) :
    literalV10Helper (withArrayFromFn ops replacement) q g slot =
      literalV10Helper ops q g slot := by
  cases ops
  cases replacement
  rfl

theorem literalV10Outer_arrayFromFn_irrelevant
    (ops replacement : Ops) (q : Slice Aeneas.Std.U8)
    (g : Array V10Wide 29#usize) :
    AspisR1FastDotsV10LiteralOuterTransferRootV1.literalV10Outer
      (withArrayFromFn ops replacement) q g =
    AspisR1FastDotsV10LiteralOuterTransferRootV1.literalV10Outer ops q g := by
  cases ops
  cases replacement
  rfl

#print axioms adaptOps_arrayFromFn_irrelevant
#print axioms v10HeadBody_arrayFromFn_irrelevant
#print axioms v10HeadLoop_arrayFromFn_irrelevant
#print axioms literalV10Helper_arrayFromFn_irrelevant
#print axioms literalV10Outer_arrayFromFn_irrelevant
end AspisR1FastDotsV10DeadArrayFromFnSlotV1
