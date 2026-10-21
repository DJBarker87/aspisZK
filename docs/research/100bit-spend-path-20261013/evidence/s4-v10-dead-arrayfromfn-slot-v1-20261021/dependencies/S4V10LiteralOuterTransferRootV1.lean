import S4FourWrapperCarrierTransportRootV1
import S4V10LiteralHelperSourceCutV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace AspisR1FastDotsV10LiteralOuterTransferRootV1
open AspisR1FastDotsV10CarrierMapV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1FastDotsV10LiteralHelperSourceCutV1 (literalV10Helper)
open AspisR1S4FourWrapperCarrierTransportRootV1 (fourWrapper mapArray)
open AspisR1FastDotsV10TailMapRootV1 (mapRes)
abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact
abbrev Wide := AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact

/-- Source-shaped candidate outer body; all four helper calls are retained in
order. Its separate source cut identifies this wrapper with emitted V10. -/
def literalV10Outer (ops : Ops) (q : Slice U8) (g : Array V10Wide 29#usize) :
    Result (Array V10Wide 4#usize) := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U8) q { «end» := 608#usize }
  let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
  let q1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let we ← literalV10Helper ops q1 g 0#usize
  let we1 ← literalV10Helper ops q1 g 1#usize
  let we2 ← literalV10Helper ops q1 g 2#usize
  let we3 ← literalV10Helper ops q1 g 3#usize
  ok (Array.make 4#usize [ we, we1, we2, we3 ])

theorem literal_outer_eq_wrapper (ops : Ops) (q : Slice U8)
    (g : Array V10Wide 29#usize) :
    literalV10Outer ops q g = fourWrapper (literalV10Helper ops) q g := rfl

private theorem mapRes_roundtrip (r : Result Wide) :
    mapRes wideToEbyK (mapRes wideFromEbyK r) = r := by
  cases r with
  | ok x => simp only [mapRes, wide_roundtrip']
  | fail e => rfl
  | div => rfl

/-- Complete four-call all-result equality, with the complete helper theorem
supplying the generic child relation rather than assuming it independently. -/
theorem literal_outer_to_current (ops : Ops) (q : Slice U8)
    (g : Array V10Wide 29#usize) :
    mapRes (mapArray wideToEbyK) (literalV10Outer ops q g) =
      AspisR1FastDotsCurrent.fast_dots.four_dots_fixed ops q (mapWideArray g) := by
  rw [literal_outer_eq_wrapper, AspisR1S4FourWrapperCarrierTransportRootV1.current_outer_eq_wrapper]
  apply AspisR1S4FourWrapperCarrierTransportRootV1.four_wrapper_map_all
  intro prefixQ slot
  have h := congrArg (mapRes wideToEbyK)
    (AspisR1FastDotsV10LiteralHelperSourceCutV1.literal_helper_eq_fixed ops prefixQ g slot)
  exact (h.trans (mapRes_roundtrip _)).symm

/-- A successful candidate outer call gives the exact same mapped output
array of the current fixed-v6 outer call; no second execution is assumed. -/
theorem literal_outer_success_current (ops : Ops) (q : Slice U8)
    (g : Array V10Wide 29#usize) (out : Array V10Wide 4#usize)
    (hcall : literalV10Outer ops q g = .ok out) :
    AspisR1FastDotsCurrent.fast_dots.four_dots_fixed ops q (mapWideArray g) =
      .ok (mapArray wideToEbyK out) := by
  have h := literal_outer_to_current ops q g
  rw [hcall] at h
  exact h.symm

#print axioms literal_outer_to_current
#print axioms literal_outer_success_current
end AspisR1FastDotsV10LiteralOuterTransferRootV1
