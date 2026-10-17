import PoseidonLeadingSourceDeclarations

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::poseidon2::EXTERNAL_INITIAL]
    Source: 'src/statement/poseidon2.rs', lines 83:0-104:2 -/
@[global_simps, irreducible]
def poseidon2.EXTERNAL_INITIAL : Array (Array Std.U32 16#usize) 4#usize :=
  Array.make 4#usize [
    Array.make 16#usize [
      1988864850#u32, 1893772157#u32, 1025928330#u32, 1839472709#u32,
      1611656994#u32, 1104858731#u32, 1694088660#u32, 1564660990#u32,
      1991332205#u32, 1875486487#u32, 1890340790#u32, 1658614#u32,
      582370530#u32, 528029397#u32, 1196956642#u32, 655401251#u32
      ],
    Array.make 16#usize [
      1652877415#u32, 26032894#u32, 1576640243#u32, 1277052539#u32,
      1450142396#u32, 697623591#u32, 1401580866#u32, 1568404175#u32,
      2145004971#u32, 265835716#u32, 1183985610#u32, 1031234465#u32,
      436012490#u32, 172735299#u32, 352802897#u32, 1032863094#u32
      ],
    Array.make 16#usize [
      757665783#u32, 1082171296#u32, 1507509996#u32, 309929890#u32,
      1807683232#u32, 43258895#u32, 611592566#u32, 1854193793#u32,
      575164234#u32, 894217817#u32, 72613857#u32, 1061659596#u32, 8921166#u32,
      1617355017#u32, 998001536#u32, 1800758877#u32
      ],
    Array.make 16#usize [
      1002748055#u32, 1935405944#u32, 1351462722#u32, 411368491#u32,
      1913975372#u32, 1956167178#u32, 442558016#u32, 855898408#u32,
      699687798#u32, 1553382248#u32, 1708169125#u32, 490049183#u32,
      1251643415#u32, 1193594742#u32, 880473871#u32, 511174042#u32
      ]
    ]

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_m31_constants_packed]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 379:4-382:5 -/
@[rust_loop]
def state_only_poseidon.full_round_m31_constants_packed_loop
  (iter : core.ops.range.Range Std.Usize) (state : Array field.QM31 16#usize)
  (constants1 : Array Std.U32 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let i ← Array.index_usize constants1 lane
    let m ← field.M31.add q.c0.a i
    let (q1, index_mut_back) ← Array.index_mut_usize state lane
    let state1 := index_mut_back { q1 with c0 := { q1.c0 with a := m } }
    let q2 ← Array.index_usize state1 lane
    let q3 ← state_only_poseidon.pow5 q2
    let a ← Array.update state1 lane q3
    state_only_poseidon.full_round_m31_constants_packed_loop iter1 a constants1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_m31_constants_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 375:0-384:1 -/
def state_only_poseidon.full_round_m31_constants_packed
  (state : Array field.QM31 16#usize) (constants1 : Array Std.U32 16#usize) :
  Result (Array field.QM31 4#usize)
  := do
  let state1 ←
    state_only_poseidon.full_round_m31_constants_packed_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state
      constants1
  state_only_poseidon.external_linear_packed state1

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_m31_constants]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 355:4-358:5 -/
@[rust_loop]
def state_only_poseidon.full_round_m31_constants_loop
  (iter : core.ops.range.Range Std.Usize) (state : Array field.QM31 16#usize)
  (constants1 : Array Std.U32 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let i ← Array.index_usize constants1 lane
    let m ← field.M31.add q.c0.a i
    let (q1, index_mut_back) ← Array.index_mut_usize state lane
    let state1 := index_mut_back { q1 with c0 := { q1.c0 with a := m } }
    let q2 ← Array.index_usize state1 lane
    let q3 ← state_only_poseidon.pow5 q2
    let a ← Array.update state1 lane q3
    state_only_poseidon.full_round_m31_constants_loop iter1 a constants1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::full_round_m31_constants]:
    Source: 'src/statement/state_only_poseidon.rs', lines 351:0-361:1 -/
def state_only_poseidon.full_round_m31_constants
  (state : Array field.QM31 16#usize) (constants1 : Array Std.U32 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let state1 ←
    state_only_poseidon.full_round_m31_constants_loop
      { start := 0#usize, «end» := poseidon2.POSEIDON2_WIDTH } state
      constants1
  state_only_poseidon.external_linear_lazy state1

/-- [aspis_r1_mask_extraction_probe::poseidon2::RATE]
    Source: 'src/statement/poseidon2.rs', lines 57:0-57:26
    Visibility: public -/
@[global_simps, irreducible] def poseidon2.RATE : Std.Usize := 8#usize

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::leading_pair_packed]: loop 0:
    Source: 'src/statement/state_only_poseidon.rs', lines 409:4-411:5 -/
@[rust_loop]
def state_only_poseidon.leading_pair_packed_loop
  (iter : core.ops.range.Range Std.Usize) (a : Array field.QM31 16#usize)
  (state : Array field.QM31 16#usize) :
  Result (Array field.QM31 16#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok state
  | some lane =>
    let q ← Array.index_usize state lane
    let q1 ← Array.index_usize a lane
    let q2 ← field.QM31.add q q1
    let a1 ← Array.update state lane q2
    state_only_poseidon.leading_pair_packed_loop iter1 a a1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::leading_pair_packed]:
    Source: 'src/statement/state_only_poseidon.rs', lines 405:0-417:1 -/
def state_only_poseidon.leading_pair_packed
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings) :
  Result (Array field.QM31 4#usize)
  := do
  let state ←
    state_only_poseidon.leading_pair_packed_loop
      { start := 0#usize, «end» := poseidon2.RATE } openings.xor12_z
      openings.z
  let state1 ← state_only_poseidon.external_linear_lazy state
  let a ← Array.index_usize poseidon2.EXTERNAL_INITIAL 0#usize
  let a1 ← state_only_poseidon.full_round_m31_constants state1 a
  let a2 ← Array.index_usize poseidon2.EXTERNAL_INITIAL 1#usize
  state_only_poseidon.full_round_m31_constants_packed a1 a2


end AspisR1SelectedMaskProbe
