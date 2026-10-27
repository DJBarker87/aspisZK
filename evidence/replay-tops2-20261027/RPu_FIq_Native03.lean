import RPu_FIq_Native02
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2086:74-2086:100 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure
  Std.Usize field.QM31 := {
  call_once :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2086:74-2086:100 -/
@[reducible]
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure
  Std.Usize field.QM31 := {
  FnOnceInst :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::withdrawal_public]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1345:0-1361:1 -/
def pool_v1.pair_forest_semantic_terminal.withdrawal_public
  (public1 : pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant :=
        pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal,
      pool := public1.pool,
      deployment_domain := public1.deployment_domain,
      anchor := public1.anchor_root,
      nullifier := public1.nullifier,
      asset_id := public1.asset_id,
      recipient := none,
      change := public1.change_commitment,
      withdrawal_amount := (some public1.amount),
      transition
    }

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::private_public]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1327:0-1343:1 -/
def pool_v1.pair_forest_semantic_terminal.private_public
  (public1 : pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
  (transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  ok
    {
      variant :=
        pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer,
      pool := public1.pool,
      deployment_domain := public1.deployment_domain,
      anchor := public1.anchor_root,
      nullifier := public1.nullifier,
      asset_id := public1.asset_id,
      recipient := (some public1.recipient_commitment),
      change := public1.change_commitment,
      withdrawal_amount := none,
      transition
    }

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::semantic]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2005:8-2010:9 -/
def pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
  (self : pool_v1.pair_forest_semantic_terminal.r0.Public) :
  Result pool_v1.pair_forest_semantic_terminal.SemanticPublic
  := do
  match self with
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Transfer public1 transition
    =>
    pool_v1.pair_forest_semantic_terminal.private_public public1 transition
  | pool_v1.pair_forest_semantic_terminal.r0.Public.Withdrawal public1
    transition =>
    pool_v1.pair_forest_semantic_terminal.withdrawal_public public1 transition

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'_0, '_1, '_2, '_3, '_4, '_5>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 605:50-621:5 -/
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c :
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
  := do
  let (sopo, a, pqm, a1, a2, a3) := c
  let start ← 4#usize * tupled_args
  let i ← start + 4#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice field.QM31)) sopo.succ_z
      { start, «end» := i }
  let target ← field.qm31_pack_base4 s
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice field.QM31)) a
      { start, «end» := i }
  let internal ← field.qm31_pack_base4 s1
  let q ← Array.index_usize a2 tupled_args
  let q1 ← field.QM31.sub target q
  let q2 ← Array.index_usize a3 tupled_args
  let q3 ← field.QM31.sub target q2
  let q4 ← field.QM31.sub target internal
  let q5 ←
    field.qm31_sum_products3_prepared a1 (Array.make 3#usize [ q1, q3, q4 ])
  let q6 ← field.PreparedQm31Multiplier.mul pqm q5
  ok (q6, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'_0, '_1, '_2, '_3, '_4, '_5>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 605:50-621:5 -/
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
  (c :
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
  (i : Std.Usize) :
  Result field.QM31
  := do
  let (q, _) ←
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
      c i
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'_0, '_1, '_2, '_3, '_4, '_5>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 605:50-621:5 -/
@[reducible]
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  : core.ops.function.FnOnce
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2
  Std.Usize field.QM31 := {
  call_once :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#2<'_0, '_1, '_2, '_3, '_4, '_5>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 605:50-621:5 -/
@[reducible]
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
  : core.ops.function.FnMut
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2
  Std.Usize field.QM31 := {
  FnOnceInst :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(aspis_r1_mask_extraction_probe::field::QM31, usize), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'_0>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 598:53-598:93 -/
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
  (c :
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1)
  (tupled_args : (field.QM31 × Std.Usize)) :
  Result (field.QM31 ×
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1)
  := do
  let (sum, row) := tupled_args
  let q ← Array.index_usize c.«local» row
  let q1 ← field.QM31.add sum q
  ok (q1, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::field::QM31, usize), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'_0>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 598:53-598:93 -/
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31.call_once
  (c :
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1)
  (p : (field.QM31 × Std.Usize)) :
  Result field.QM31
  := do
  let (q, _) ←
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::field::QM31, usize), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 598:53-598:93 -/
@[reducible]
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31
  : core.ops.function.FnOnce
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1
  (field.QM31 × Std.Usize) field.QM31 := {
  call_once :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(aspis_r1_mask_extraction_probe::field::QM31, usize), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure#1<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 598:53-598:93 -/
@[reducible]
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
  : core.ops.function.FnMut
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1
  (field.QM31 × Std.Usize) field.QM31 := {
  FnOnceInst :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31
  call_mut :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_1.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(aspis_r1_mask_extraction_probe::field::QM31, usize), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'_0>}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 597:26-597:66 -/
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
  (c :
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure)
  (tupled_args : (field.QM31 × Std.Usize)) :
  Result (field.QM31 ×
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure)
  := do
  let (sum, row) := tupled_args
  let q ← Array.index_usize c.«local» row
  let q1 ← field.QM31.add sum q
  ok (q1, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::field::QM31, usize), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'_0>}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 597:26-597:66 -/
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31.call_once
  (c :
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure)
  (p : (field.QM31 × Std.Usize)) :
  Result field.QM31
  := do
  let (q, _) ←
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
      c p
  ok q

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnOnce<(aspis_r1_mask_extraction_probe::field::QM31, usize), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 597:26-597:66 -/
@[reducible]
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31
  : core.ops.function.FnOnce
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure
  (field.QM31 × Std.Usize) field.QM31 := {
  call_once :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::{impl core::ops::function::FnMut<(aspis_r1_mask_extraction_probe::field::QM31, usize), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::state_only_poseidon::evaluate_state_only_poseidon_oracle_projected::closure<'_0>}]
    Source: 'src/statement/state_only_poseidon.rs', lines 597:26-597:66 -/
@[reducible]
def
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31
  : core.ops.function.FnMut
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure
  (field.QM31 × Std.Usize) field.QM31 := {
  FnOnceInst :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnOncePairQM31UsizeQM31
  call_mut :=
    state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure.Insts.CoreOpsFunctionFnMutPairQM31UsizeQM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::poseidon2::INTERNAL]
    Source: 'src/statement/poseidon2.rs', lines 129:0-132:2 -/
@[global_simps, irreducible]
def poseidon2.INTERNAL : Array Std.U32 14#usize :=
  Array.make 14#usize [
    2139014335#u32, 69309039#u32, 1368974953#u32, 886780232#u32,
    1130937085#u32, 1718115455#u32, 2027103386#u32, 1612216449#u32,
    1994053242#u32, 110146615#u32, 514413329#u32, 1088763546#u32,
    955319292#u32, 488794657#u32
    ]

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 536:33-536:71 -/
def
  state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : state_only_poseidon.interpolated_internal_pair.closure_2)
  (tupled_args : Std.Usize) :
  Result (field.M31 ×
    state_only_poseidon.interpolated_internal_pair.closure_2)
  := do
  let i ← tupled_args - 2#usize
  let i1 ← 2#usize * i
  let i2 ← i1 + 1#usize
  let i3 ← Array.index_usize poseidon2.INTERNAL i2
  ok (i3, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 536:33-536:71 -/
def
  state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : state_only_poseidon.interpolated_internal_pair.closure_2)
  (i : Std.Usize) :
  Result field.M31
  := do
  let (m, _) ←
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2}]
    Source: 'src/statement/state_only_poseidon.rs', lines 536:33-536:71 -/
@[reducible]
def
  state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce
  state_only_poseidon.interpolated_internal_pair.closure_2 Std.Usize field.M31
  := {
  call_once :=
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}

/-- Trait implementation: [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#2}]
    Source: 'src/statement/state_only_poseidon.rs', lines 536:33-536:71 -/
@[reducible]
def
  state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut
  state_only_poseidon.interpolated_internal_pair.closure_2 Std.Usize field.M31
  := {
  FnOnceInst :=
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    state_only_poseidon.interpolated_internal_pair.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#1}::call_mut]:
    Source: 'src/statement/state_only_poseidon.rs', lines 535:34-535:68 -/
def
  state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
  (c : state_only_poseidon.interpolated_internal_pair.closure_1)
  (tupled_args : Std.Usize) :
  Result (field.M31 ×
    state_only_poseidon.interpolated_internal_pair.closure_1)
  := do
  let i ← tupled_args - 2#usize
  let i1 ← 2#usize * i
  let i2 ← Array.index_usize poseidon2.INTERNAL i1
  ok (i2, c)

/-- [aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::{impl core::ops::function::FnOnce<(usize,), aspis_r1_mask_extraction_probe::field::M31> for aspis_r1_mask_extraction_probe::state_only_poseidon::interpolated_internal_pair::closure#1}::call_once]:
    Source: 'src/statement/state_only_poseidon.rs', lines 535:34-535:68 -/
def
  state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : state_only_poseidon.interpolated_internal_pair.closure_1)
  (i : Std.Usize) :
  Result field.M31
  := do
  let (m, _) ←
    state_only_poseidon.interpolated_internal_pair.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m


end FIq_Native
