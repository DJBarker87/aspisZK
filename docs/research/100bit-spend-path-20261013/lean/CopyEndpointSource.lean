import SameBoxedRowExact
import TerminalLiftM31Exact
import ExtractedMaskScalarExact
import ArrayUpdateCanonicalExact
import R0P.Copy

/-! Exact endpoint accumulation source and carrier from sealed04fc/60cf.
Shared checked arithmetic and selector owners are imported, not replaced. -/
set_option autoImplicit false
namespace AspisR1CopyEndpointCandidate
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

structure pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestEndpoint
  where
  row : Std.U16
  slot : Std.U8
  pattern : Std.U8

def pool_v1.pair_forest_copy_terminal.lift_m31
  (value : field.M31) : Result field.QM31 := do
  let c ← field.CM31.from_m31 value
  field.QM31.from_cm31 c

def pool_v1.pair_forest_copy_terminal.accumulate_endpoint
  (values : Array field.QM31 2#usize) (weights : Array field.QM31 2#usize)
  (endpoint :
  pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestEndpoint)
  (tag : Std.U32) (weight : field.M31) (patterns : Array field.QM31 14#usize)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result ((Array field.QM31 2#usize) × (Array field.QM31 2#usize))
  := do
  let i ← lift (core.convert.num.FromUsizeU16.from endpoint.row)
  let selector ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i
  let slot ← lift (core.convert.num.FromUsizeU8.from endpoint.slot)
  let q ← Array.index_usize weights slot
  let q1 ← field.QM31.mul_m31 selector weight
  let q2 ← field.QM31.add q q1
  let weights1 ← Array.update weights slot q2
  let q3 ← pool_v1.pair_forest_copy_terminal.lift_m31 tag
  let i1 ← lift (core.convert.num.FromUsizeU8.from endpoint.pattern)
  let q4 ← Array.index_usize patterns i1
  let compressed ← field.QM31.add q3 q4
  let q5 ← Array.index_usize values slot
  let q6 ← field.QM31.mul selector compressed
  let q7 ← field.QM31.add q5 q6
  let values1 ← Array.update values slot q7
  ok (values1, weights1)

end AspisR1CopyEndpointCandidate
