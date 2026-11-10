-- PCWL_ AdapterRwModel require_zero: fresh (frozen 4bb3b3f, slice loop `while !remaining.is_empty()`) = gate (index loop `index < bytes.len()`), all inputs.
-- SOURCE DIFFERENCE (not an encoding difference): the gate's require_zero is an index-based loop; the frozen function loops over `remaining = &remaining[1..]`.
-- Fresh text: PCWL_E001 emission (original Aeneas 959659a6, overflow ON, Charon cargo --jobs 4, identity by class receipt PCWE_E003): require_zero_loop.body, require_zero_loop, require_zero.
-- The gate's require_zero_loop and require_zero_loop.body have no frozen counterpart (different loop state); they are cleared only through the parent equality below.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AdapterRw
namespace PRVFresh_ARM_w7

