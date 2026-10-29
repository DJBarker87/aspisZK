import PV_B3P_Operations12227
import PV_B3P_RangeFold13227
import PV_B3P_Success227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

abbrev PathState15 := Array aspis_core.field.QM31 17#usize
/-- Each source iteration repeats both the ONE-bit subtraction and the
path_selector*bit product. They are NOT silently cached in this interpreter. -/
def path_step15 (path_selector : aspis_core.field.QM31)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (bit : aspis_core.field.QM31) (state : PathState15) (lane : Usize) : Result PathState15 := do
  let source ← lift (Usize.wrapping_add 1#usize lane)
  let current ← Array.index_usize openings.z source
  let minus ← aspis_core.field.QM31.sub aspis_core.field.QM31.ONE bit
  let left ← aspis_core.field.QM31.mul path_selector minus
  let next ← Array.index_usize openings.succ_z lane
  let diff ← aspis_core.field.QM31.sub next current
  let weighted ← aspis_core.field.QM31.mul left diff
  let target ← lift (Usize.wrapping_add 1#usize lane)
  let state1 ← Array.update state target weighted
  let right ← aspis_core.field.QM31.mul path_selector bit
  let source1 ← lift (Usize.wrapping_add aspis_statement.poseidon2.RATE lane)
  let next1 ← Array.index_usize openings.succ_z source1
  let diff1 ← aspis_core.field.QM31.sub next1 current
  let weighted1 ← aspis_core.field.QM31.mul right diff1
  let base ← lift (Usize.wrapping_add 1#usize aspis_statement.poseidon2.DIGEST_ELEMS)
  let target1 ← lift (Usize.wrapping_add base lane)
  Array.update state1 target1 weighted1
end PV_B3P_Native15227
