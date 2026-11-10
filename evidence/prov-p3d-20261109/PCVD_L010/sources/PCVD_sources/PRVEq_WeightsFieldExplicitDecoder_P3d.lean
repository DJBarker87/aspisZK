-- PCVD_ item 2 (instance boundary): fresh `weights::field` (PCQF_E006 text) with its two external constants
-- (`aspis_core.field.wide_exact.WideExact` : Type and `WideExact.from_le_bytes`, both opaque `axiom`s in the
-- cross-crate emission's External templates) taken as parameters.  The gate `weights.field` is generic in exactly these two.
-- Statement: for every type W and decoder d the fresh body equals the gate body.  The binding W := WideExact, d := from_le_bytes
-- is the consumer's instantiation and is NOT proved here (hand-model/transparent-emission question for P6).
import Aeneas
import WeightsFieldExplicitDecoder
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1WeightsFieldCurrent
namespace PRVFresh_WeightsFieldExplicitDecoder

/-- [aspis_r1_cost_probe::weights::field]  (fresh text; externals WideExact / WideExact.from_le_bytes abstracted as parameters W / d)
    Source: 'crates/aspis-r1-cost-probe/src/weights.rs', lines 25:0-25:90 -/
def weights.field
  {W : Type} (d : Slice Std.U8 → Result (Option W))
  (bytes : Slice Std.U8) (i : Std.Usize) :
  Result W
  := do
  let i1 ← i * 32#usize
  let i2 ← i + 1#usize
  let i3 ← i2 * 32#usize
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) bytes { start := i1, «end» := i3 }
  let o ← d s
  core.option.Option.unwrap o

end PRVFresh_WeightsFieldExplicitDecoder
end AspisR1WeightsFieldCurrent

set_option maxHeartbeats 200000 in
theorem PRVD.Eq.weights.field {W : Type} (d : Slice Std.U8 → Result (Option W)) :
    @AspisR1WeightsFieldCurrent.PRVFresh_WeightsFieldExplicitDecoder.weights.field W d = @AspisR1WeightsFieldCurrent.weights.field W d := by
  delta AspisR1WeightsFieldCurrent.PRVFresh_WeightsFieldExplicitDecoder.weights.field AspisR1WeightsFieldCurrent.weights.field
  rfl
#print axioms PRVD.Eq.weights.field
