-- Exact generated wrapper declaration extracted from the pinned from_fn-copy candidate.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import ArrayFromFnCopySlice
import RowCallbackSlice
import RawPoseidonExtensionSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::external_linear_lazy_row]:
    Source: 'src/statement/state_only_poseidon.rs', lines 143:0-158:1 -/
def state_only_poseidon.external_linear_lazy_row
  (input : Array (Array Std.U32 4#usize) 4#usize) (output : Std.Usize) :
  Result field.QM31
  := do
  let raw1 ←
    array_from_fn_copy 4#usize core.marker.CopyU64
      state_only_poseidon.external_linear_lazy_row.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64
      0#u64 (input, output)
  state_only_poseidon.extension_from_raw_limbs raw1


end AspisR1SelectedMaskProbe
