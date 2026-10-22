import S4TraceLiteralOutputJoinV1
import S4PairFunctionViewsV1
import Query31SourceCalls
import Query31MathematicalSchedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.S4Row31SourceTraceConsumerV1
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisR1PublicPreparation.Query31SourceSchedule
open AspisR1PublicPreparation.R4Transport2QueryPrefix
open AspisR1.S4SourcePairsToFunctionsV1
open AspisV8R19.SqueezeOracleBridge

/-- The literal sampler's same-pair result and the actual materialized scan
    result agree on the output words. The materialized output witness itself
    supplies the pair-to-array views; the trace result is for those same arrays.
    Prefix/digest assumptions used to obtain `hpairs` remain at the caller. -/
theorem row31_source_trace_output
    {Hash : Type} {D : aspis_core.Digest32 Hash} {hash : Hash}
    (sourcePairs : List (DigestPair D hash))
    (initial : Array U8 32#usize)
    (blocks advances : Array (Array U8 32#usize) 8#usize)
    (xs : List Nat) (out : Array U32 22#usize)
    (hmaterial : materializedOutputs sourcePairs blocks advances)
    (hpairs : (R4Transport2ScanComposition.pairsRun R0C.V3.Q22.q0
      (R4Transport2QueryPrefix.pairs
        (fun k => decodeState (sourcePairBlocks sourcePairs initial k))
        (fun k => decodeState (sourcePairStates sourcePairs initial k)))
      (decodeState initial)).1 = .ok xs)
    (htrace : (R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0
      (blocks.val.map decodeState) (advances.val.map decodeState)
      (decodeState initial)).1 = .ok (out.val.map (fun w => w.val))) :
    out.val.map (fun w => w.val) = xs := by
  let blockFn : Nat → AspisV8R19.SourceDuplexStep.State :=
    fun k => decodeState (sourcePairBlocks sourcePairs initial k)
  let stateFn : Nat → AspisV8R19.SourceDuplexStep.State :=
    fun k => decodeState (sourcePairStates sourcePairs initial k)
  have hviews0 := AspisR1.S4PairFunctionViewsV1.materialized_pair_function_views
    sourcePairs initial blocks advances hmaterial
  have hviews :
      (R4Transport2QueryPrefix.pairs blockFn stateFn).map Prod.fst = blocks.val.map decodeState ∧
      (R4Transport2QueryPrefix.pairs blockFn stateFn).map Prod.snd = advances.val.map decodeState := by
    constructor
    · change (List.range 8).map blockFn = blocks.val.map decodeState
      exact hviews0.1.symm
    · change (List.range 8).map (fun k => stateFn (k+1)) = advances.val.map decodeState
      exact hviews0.2.symm
  exact AspisR1.S4TraceLiteralOutputJoinV1.literal_list_eq_trace_values
    (R4Transport2QueryPrefix.pairs blockFn stateFn) (decodeState initial) xs
    (blocks.val.map decodeState) (advances.val.map decodeState) out
    (decodeState initial) (by simp [R4Transport2QueryPrefix.pairs]) hpairs hviews htrace

#print axioms row31_source_trace_output
end AspisR1.S4Row31SourceTraceConsumerV1
end
