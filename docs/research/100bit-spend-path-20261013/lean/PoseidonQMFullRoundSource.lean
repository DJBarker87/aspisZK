import PoseidonLeadingSourceDeclarationsV5

/-! Exact missing QM-constant full-round source declarations from candidate Funs f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c. -/
namespace AspisR1SelectedMaskProbe
open Aeneas Aeneas.Std Result

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 364:0-372:1 -/
def state_only_poseidon.full_round_packed
  (state : Array field.QM31 16#usize) (constants1 : Array field.QM31 16#usize)
  :
  Result (Array field.QM31 4#usize)
  := do
  let state1 ←
    state_only_poseidon.full_round_packed_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state
      constants1
  state_only_poseidon.external_linear_packed state1


/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 340:4-342:5 -/
@[rust_loop]
def state_only_poseidon.full_round_loop
  (iter : core.ops.range.Range Std.Usize) (state : Array field.QM31 16#usize)
  (constants1 : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let q1 ← Array.index_usize constants1 lane
    let q2 ← field.QM31.add q q1
    let q3 ← state_only_poseidon.pow5 q2
    let a ← Array.update state lane q3
    state_only_poseidon.full_round_loop iter1 a constants1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round]:
    Source: 'src/statement/state_only_poseidon.rs', lines 336:0-345:1 -/
def state_only_poseidon.full_round
  (state : Array field.QM31 16#usize) (constants1 : Array field.QM31 16#usize)
  :
  Result (Array field.QM31 16#usize)
  := do
  let state1 ←
    state_only_poseidon.full_round_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state
      constants1
  state_only_poseidon.external_linear_lazy state1


end AspisR1SelectedMaskProbe
