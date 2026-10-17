import PoseidonThreeConstantColumnsSource
import PoseidonQMFullRoundSource

/-! Exact missing enclosing wrapper from candidate Funs f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c. Existing source operation owners are imported unchanged. -/
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result
/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_full_pair_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 508:0-526:1 -/
def state_only_poseidon.interpolated_full_pair_packed
  (state : Array field.QM31 16#usize) (local1 : Array field.QM31 16#usize) :
  Result (Array field.QM31 4#usize)
  := do
  let q ← Array.index_usize local1 1#usize
  let q1 ← Array.index_usize local1 9#usize
  let q2 ← Array.index_usize local1 10#usize
  let a ← Array.index_usize poseidon2.EXTERNAL_INITIAL 2#usize
  let a1 ← Array.index_usize poseidon2.EXTERNAL_FINAL 0#usize
  let a2 ← Array.index_usize poseidon2.EXTERNAL_FINAL 2#usize
  let even ←
    state_only_poseidon.interpolate_three_constant_columns
      (Array.make 3#usize [ q, q1, q2 ]) a a1 a2
  let a3 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 3#usize
  let a4 ← Array.index_usize poseidon2.EXTERNAL_FINAL 1#usize
  let a5 ← Array.index_usize poseidon2.EXTERNAL_FINAL 3#usize
  let odd ←
    state_only_poseidon.interpolate_three_constant_columns
      (Array.make 3#usize [ q, q1, q2 ]) a3 a4 a5
  let a6 ← state_only_poseidon.full_round state even
  state_only_poseidon.full_round_packed a6 odd


end AspisR1SelectedMaskProbe
