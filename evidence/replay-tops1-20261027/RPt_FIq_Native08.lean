import RPt_FIq_Native07
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1257:58-1257:100 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure Std.Usize
  field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts::closure<'_0>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1257:58-1257:100 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.composition_parts.closure Std.Usize
  field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.composition_parts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::copy_variant]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1208:0-1213:1 -/
def pool_v1.pair_forest_semantic_terminal.copy_variant
  (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant) :
  Result pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
  := do
  match variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    ok
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    ok
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Withdrawal

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::scalar_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1136:0-1155:1 -/
def pool_v1.pair_forest_semantic_terminal.scalar_lanes
  (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant)
  (withdrawal_amount_present : Bool) (input_asset : field.QM31)
  (output_scalar : field.QM31) (private_transfer_term : field.QM31)
  (withdrawal_term : field.QM31) :
  Result (Array field.QM31 2#usize)
  := do
  match variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    let output_scalar1 ← field.QM31.add output_scalar private_transfer_term
    ok (Array.make 2#usize [ input_asset, output_scalar1 ])
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    if withdrawal_amount_present
    then
      let output_scalar1 ← field.QM31.add output_scalar withdrawal_term
      ok (Array.make 2#usize [ input_asset, output_scalar1 ])
    else ok (Array.make 2#usize [ input_asset, output_scalar ])

/-- [aspis_r1_mask_extraction_probe::poseidon2::MERKLE_NODE_COMPRESSION_V3_TWEAK]
    Source: 'src/statement/poseidon2.rs', lines 465:0-465:67
    Visibility: public -/
@[global_simps, irreducible]
def poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK : field.M31 := 1095962629#u32

/-- [aspis_r1_mask_extraction_probe::poseidon2::DIGEST_ELEMS]
    Source: 'src/statement/poseidon2.rs', lines 58:0-58:34
    Visibility: public -/
@[global_simps, irreducible] def poseidon2.DIGEST_ELEMS : Std.Usize := 8#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::lift_m31]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 101:0-103:1 -/
def pool_v1.pair_forest_semantic_terminal.lift_m31
  (value : field.M31) : Result field.QM31 := do
  let c ← field.CM31.from_m31 value
  field.QM31.from_cm31 c

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_digest_binding]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 386:4-392:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.add_digest_binding_loop
  (iter : core.ops.range.Range Std.Usize) (output : Array field.QM31 8#usize)
  (selector : field.QM31) (opened : Array field.QM31 16#usize)
  (start : Std.Usize) (expected : Array field.M31 8#usize) (right_tweak : Bool)
  :
  Result (Array field.QM31 8#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok output
  | some lane =>
    let target ← Array.index_usize expected lane
    let (iter2, target1) ←
      if right_tweak
      then
        do
        let i ← lane + 1#usize
        let m ←
          if i = poseidon2.DIGEST_ELEMS
          then field.M31.add target poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK
          else ok target
        ok (iter1, m)
      else ok (iter1, target)
    let q ← Array.index_usize output lane
    let i ← start + lane
    let q1 ← Array.index_usize opened i
    let q2 ← pool_v1.pair_forest_semantic_terminal.lift_m31 target1
    let q3 ← field.QM31.sub q1 q2
    let q4 ← field.QM31.mul selector q3
    let q5 ← field.QM31.add q q4
    let a ← Array.update output lane q5
    pool_v1.pair_forest_semantic_terminal.add_digest_binding_loop iter2 a
      selector opened start expected right_tweak
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_digest_binding]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 378:0-393:1 -/
@[reducible]
def pool_v1.pair_forest_semantic_terminal.add_digest_binding
  (output : Array field.QM31 8#usize) (selector : field.QM31)
  (opened : Array field.QM31 16#usize) (start : Std.Usize)
  (expected : Array field.M31 8#usize) (right_tweak : Bool) :
  Result (Array field.QM31 8#usize)
  := do
  pool_v1.pair_forest_semantic_terminal.add_digest_binding_loop
    { start := 0#usize, «end» := poseidon2.DIGEST_ELEMS } output selector
    opened start expected right_tweak

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::constants::POOL_V1_PAIR_EMPTY_ROOTS_V1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal_constants.rs', lines 2:0-24:2
    Visibility: public -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
  : Array (Array Std.U32 8#usize) 21#usize :=
  Array.make 21#usize [
    Array.make 8#usize [
      1438900896#u32, 782233260#u32, 1544844157#u32, 891350894#u32,
      986827501#u32, 300047813#u32, 266092546#u32, 1155026732#u32
      ],
    Array.make 8#usize [
      141619947#u32, 1448060902#u32, 524379093#u32, 1944458907#u32,
      1832113773#u32, 579270723#u32, 752346270#u32, 1038346536#u32
      ],
    Array.make 8#usize [
      1119858538#u32, 128294437#u32, 939091034#u32, 659145897#u32,
      1933666768#u32, 903679201#u32, 1182639487#u32, 1398246146#u32
      ],
    Array.make 8#usize [
      1057897051#u32, 1132946363#u32, 794377079#u32, 1971564389#u32,
      1255722275#u32, 926653737#u32, 2031728153#u32, 2024887573#u32
      ],
    Array.make 8#usize [
      1410054462#u32, 673771449#u32, 940847521#u32, 274330358#u32,
      1719505495#u32, 1690439941#u32, 203201419#u32, 1855504616#u32
      ],
    Array.make 8#usize [
      1442759752#u32, 1540325866#u32, 188964047#u32, 101815282#u32,
      1883549730#u32, 1774537487#u32, 1306717763#u32, 561084592#u32
      ],
    Array.make 8#usize [
      244193611#u32, 984304317#u32, 1467689208#u32, 2063463197#u32,
      1766003332#u32, 1300835127#u32, 1578947755#u32, 745931587#u32
      ],
    Array.make 8#usize [
      673192756#u32, 38070812#u32, 1453532835#u32, 1340577407#u32,
      368420458#u32, 1834405704#u32, 270061815#u32, 711700631#u32
      ],
    Array.make 8#usize [
      27092219#u32, 1272373356#u32, 998194489#u32, 1458413288#u32,
      887470405#u32, 1204987730#u32, 864453460#u32, 553704718#u32
      ],
    Array.make 8#usize [
      1972918328#u32, 1234090299#u32, 977162835#u32, 1704494754#u32,
      1617603773#u32, 1819200880#u32, 906453206#u32, 1653526885#u32
      ],
    Array.make 8#usize [
      418360492#u32, 472096212#u32, 871749117#u32, 98906847#u32,
      2026788776#u32, 1504737042#u32, 407274798#u32, 1800828893#u32
      ],
    Array.make 8#usize [
      986339640#u32, 660349625#u32, 1012157959#u32, 454024326#u32,
      987656904#u32, 622864739#u32, 1150440730#u32, 1280042062#u32
      ],
    Array.make 8#usize [
      2118470693#u32, 1706590589#u32, 2128512933#u32, 167263577#u32,
      409542414#u32, 1323179656#u32, 1880070613#u32, 2053396184#u32
      ],
    Array.make 8#usize [
      260546973#u32, 1375125357#u32, 1584234519#u32, 1097072342#u32,
      1685367984#u32, 1070989054#u32, 2113798037#u32, 958210542#u32
      ],
    Array.make 8#usize [
      1239966481#u32, 992485427#u32, 1397515674#u32, 466658549#u32,
      2071909237#u32, 712995354#u32, 2047452742#u32, 1680224983#u32
      ],
    Array.make 8#usize [
      1796237568#u32, 1862343136#u32, 1954463912#u32, 1190686266#u32,
      364700025#u32, 46960257#u32, 671215600#u32, 1214723477#u32
      ],
    Array.make 8#usize [
      1127845264#u32, 662862400#u32, 84021756#u32, 995080286#u32,
      1419670571#u32, 1966281459#u32, 837284626#u32, 2083375353#u32
      ],
    Array.make 8#usize [
      1321679286#u32, 782621548#u32, 1415820264#u32, 74436574#u32,
      776350425#u32, 323154748#u32, 429051705#u32, 1299980413#u32
      ],
    Array.make 8#usize [
      1519171444#u32, 1235587172#u32, 1671492368#u32, 1449613582#u32,
      547369941#u32, 1621086153#u32, 266860322#u32, 450526803#u32
      ],
    Array.make 8#usize [
      19381883#u32, 1308966873#u32, 251977766#u32, 474343397#u32,
      2069732268#u32, 1863820229#u32, 152153379#u32, 665567443#u32
      ],
    Array.make 8#usize [
      1201428963#u32, 1296676114#u32, 441891487#u32, 1910121140#u32,
      602621674#u32, 1294160489#u32, 1878016864#u32, 855887413#u32
      ]
    ]

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::empty_root]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 190:0-192:1 -/
def pool_v1.pair_forest_semantic_terminal.empty_root
  (level : Std.Usize) : Result (Array field.M31 8#usize) := do
  let a ←
    Array.index_usize
      pool_v1.pair_forest_semantic_terminal.constants.POOL_V1_PAIR_EMPTY_ROOTS_V1
      level
  core.array.Array.map (BuiltinFnMut Std.U32 field.M31) a
    (field.M31_constructor)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::bounded_append_carry]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 109:4-117:1 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop
  (index : Std.U64) (carry : Std.Usize) : Result Std.Usize := do
  if carry < 20#usize
  then
    let i ← lift (index &&& 1#u64)
    if i = 0#u64
    then ok carry
    else
      let index1 ← index >>> 1#u32
      let carry1 ← carry + 1#usize
      pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop index1
        carry1
  else ok carry
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::bounded_append_carry]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 107:0-117:1 -/
@[reducible]
def pool_v1.pair_forest_semantic_terminal.bounded_append_carry
  (index : Std.U64) : Result Std.Usize := do
  pool_v1.pair_forest_semantic_terminal.bounded_append_carry_loop index 0#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::row]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 174:4-177:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.row
  (self : pool_v1.pair_forest_copy_terminal.Selectors) (row : Std.Usize) :
  Result field.QM31
  := do
  let i ← row >>> 4#i32
  let q ← Array.index_usize self.high i
  let i1 ← lift (row &&& 15#usize)
  let q1 ← Array.index_usize self.low i1
  field.QM31.mul q q1

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::public_digest_lanes]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 666:4-687:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop
  (iter : core.ops.range.Range Std.Usize) (a : Array field.QM31 16#usize)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
  (digests : Array field.QM31 8#usize)
  (source : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
  Result ((Array field.QM31 8#usize) ×
    pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (digests, source)
  | some level =>
    let block ← 34#usize + level
    let i ← source.next_pair_index >>> level
    let i1 ← lift (i &&& 1#u64)
    if i1 = 0#u64
    then
      let i2 ← block * 16#usize
      let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i2
      let a1 ← pool_v1.pair_forest_semantic_terminal.empty_root level
      let digests1 ←
        pool_v1.pair_forest_semantic_terminal.add_digest_binding digests q a
          poseidon2.RATE a1 true
      pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop iter1 a
        selectors digests1 source
    else
      let i2 ← block * 16#usize
      let i3 ← i2 + 12#usize
      let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
      let a1 ← Array.index_usize source.frontier level
      let digests1 ←
        pool_v1.pair_forest_semantic_terminal.add_digest_binding digests q a
          0#usize a1 false
      pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop iter1 a
        selectors digests1 source
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::public_digest_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 623:0-708:1 -/
def pool_v1.pair_forest_semantic_terminal.public_digest_lanes
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 8#usize)
  := do
  let digests := Array.repeat 8#usize field.QM31.ZERO
  let i ← 56#usize * 16#usize
  let i1 ← i + 11#usize
  let q ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i1
  let digests1 ←
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests q
      openings.z 0#usize public1.anchor false
  let i2 ← 26#usize * 16#usize
  let i3 ← i2 + 11#usize
  let q1 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
  let digests2 ←
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests1 q1
      openings.z 0#usize public1.nullifier false
  let digests3 ←
    match public1.recipient with
    | none => ok digests2
    | some recipient =>
      do
      let i4 ← 29#usize * 16#usize
      let i5 ← i4 + 11#usize
      let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
      pool_v1.pair_forest_semantic_terminal.add_digest_binding digests2 q2
        openings.z 0#usize recipient false
  let i4 ← 32#usize * 16#usize
  let i5 ← i4 + 11#usize
  let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
  let digests4 ←
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests3 q2
      openings.z 0#usize public1.change false
  let (digests5, source) ←
    pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop
      { start := 0#usize, «end» := 20#usize } openings.z selectors digests4
      public1.transition.live_snapshot
  let i6 ← 53#usize * 16#usize
  let i7 ← i6 + 11#usize
  let q3 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i7
  let digests6 ←
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests5 q3
      openings.z 0#usize public1.transition.candidate_afterstate.next_root
      false
  let carry ←
    pool_v1.pair_forest_semantic_terminal.bounded_append_carry
      source.next_pair_index
  if carry < 20#usize
  then
    let i8 ← 33#usize + carry
    let i9 ← i8 * 16#usize
    let i10 ← i9 + 11#usize
    let q4 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i10
    let a ←
      Array.index_usize public1.transition.candidate_afterstate.next_frontier
        carry
    pool_v1.pair_forest_semantic_terminal.add_digest_binding digests6 q4
      openings.z 0#usize a false
  else ok digests6

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::occupancy_lanes_literal]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 585:4-587:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
  (iter : core.ops.range.Range Std.Usize) (opened : Array field.QM31 16#usize)
  (one_minus : field.QM31) (occupancy : Array field.QM31 12#usize)
  (both : field.QM31) :
  Result (Array field.QM31 12#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok occupancy
  | some lane =>
    let i ← 2#usize + lane
    let q ← Array.index_usize opened i
    let q1 ← field.QM31.mul one_minus q
    let q2 ← field.QM31.mul both q1
    let i1 ← 3#usize + lane
    let a ← Array.update occupancy i1 q2
    pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop iter1
      opened one_minus a both
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::occupancy_lanes_literal]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 571:0-592:1 -/
def pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal
  (input_occupancy : field.QM31) (output_occupancy : field.QM31)
  (expected_output : field.M31) (opened : Array field.QM31 16#usize) :
  Result (Array field.QM31 12#usize)
  := do
  let occupied ← Array.index_usize opened 0#usize
  let inverse ← Array.index_usize opened 1#usize
  let one_minus ← field.QM31.sub field.QM31.ONE occupied
  let occupancy := Array.repeat 12#usize field.QM31.ZERO
  let both ← field.QM31.add input_occupancy output_occupancy
  let q ← field.QM31.sub occupied field.QM31.ONE
  let q1 ← field.QM31.mul occupied q
  let q2 ← field.QM31.mul both q1
  let occupancy1 ← Array.update occupancy 0#usize q2
  let q3 ← Array.index_usize opened 9#usize
  let q4 ← field.QM31.mul q3 inverse
  let q5 ← field.QM31.sub q4 occupied
  let q6 ← field.QM31.mul both q5
  let occupancy2 ← Array.update occupancy1 1#usize q6
  let q7 ← field.QM31.mul one_minus inverse
  let q8 ← field.QM31.mul both q7
  let a ← Array.update occupancy2 2#usize q8
  let occupancy3 ←
    pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
      { start := 0#usize, «end» := poseidon2.DIGEST_ELEMS } opened one_minus
      a both
  let q9 ← Array.index_usize opened 10#usize
  let q10 ← field.QM31.mul q9 one_minus
  let q11 ← field.QM31.mul input_occupancy q10
  let q12 ← pool_v1.pair_forest_semantic_terminal.lift_m31 expected_output
  let q13 ← field.QM31.sub occupied q12
  let q14 ← field.QM31.mul output_occupancy q13
  let q15 ← field.QM31.add q11 q14
  Array.update occupancy3 11#usize q15

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::variant_expected_output]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 536:0-541:1 -/
def pool_v1.pair_forest_semantic_terminal.variant_expected_output
  (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant) :
  Result field.M31
  := do
  match variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    ok 1#u32
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    ok 0#u32

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted::closure<'_0, '_1, '_2, N>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 128:77-135:9 -/
def
  pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  {N : Std.Usize}
  (c : pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure N))
  := do
  let (i, i1, a) := c
  let i2 ← 4#usize * i
  let source ← i2 + tupled_args
  if source >= i1
  then
    let i3 ← i1 + N
    if source < i3
    then let i4 ← source - i1
         let q ← Array.index_usize a i4
         ok (q, c)
    else ok (field.QM31.ZERO, c)
  else ok (field.QM31.ZERO, c)


end FIq_Native
