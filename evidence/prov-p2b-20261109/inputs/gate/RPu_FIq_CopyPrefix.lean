import RPu_FIq_Native12
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::lift_m31]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 114:0-116:1 -/
def pool_v1.pair_forest_copy_terminal.lift_m31
  (value : field.M31) : Result field.QM31 := do
  let c ← field.CM31.from_m31 value
  field.QM31.from_cm31 c

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::accumulate_endpoint]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 438:0-464:1 -/
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{impl core::cmp::PartialEq<aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::PoolV1PairForestCompiledVariantV1> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::PoolV1PairForestCompiledVariantV1}::eq]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 67:29-67:38
    Visibility: public -/
def
  pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
  (self : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
  (other : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1)
  :
  Result Bool
  := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::link_weight]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 374:0-391:1 -/
def pool_v1.pair_forest_copy_terminal.link_weight
  (link : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestLink)
  (append_index : Std.U64)
  (variant :
  pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1) :
  Result field.M31
  := do
  match link.weight_kind with
  | 0#uscalar => ok field.M31.ONE
  | 1#uscalar =>
    let b ←
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
        variant
        pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer
    let i ← lift (core.convert.num.FromU32Bool.from b)
    ok i
  | 2#uscalar =>
    let b ←
      pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq
        variant
        pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Withdrawal
    let i ← lift (core.convert.num.FromU32Bool.from b)
    ok i
  | 3#uscalar =>
    let i ← append_index >>> link.weight_level
    let i1 ← lift (i &&& 1#u64)
    let i2 ← lift (UScalar.cast .U32 i1)
    let i3 ← 1#u32 - i2
    ok i3
  | 4#uscalar =>
    let i ← append_index >>> link.weight_level
    let i1 ← lift (i &&& 1#u64)
    let i2 ← lift (UScalar.cast .U32 i1)
    ok i2
  | _ => fail panic

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::copy_residual]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 353:0-371:1 -/
def pool_v1.pair_forest_copy_terminal.copy_residual
  (row : pool_v1.pair_forest_copy_terminal.CopyRowExtension)
  (helper : field.QM31) (chi : field.QM31) :
  Result field.QM31
  := do
  let q ← Array.index_usize row.producer_values 0#usize
  let q1 ← field.QM31.sub chi q
  let q2 ← Array.index_usize row.producer_values 1#usize
  let q3 ← field.QM31.sub chi q2
  let q4 ← Array.index_usize row.consumer_values 0#usize
  let q5 ← field.QM31.sub chi q4
  let q6 ← Array.index_usize row.consumer_values 1#usize
  let q7 ← field.QM31.sub chi q6
  let q8 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 0#usize
  let q9 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 1#usize
  let producer_denominator ← field.QM31.mul q8 q9
  let q10 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 2#usize
  let q11 ← Array.index_usize (Array.make 4#usize [ q1, q3, q5, q7 ]) 3#usize
  let consumer_denominator ← field.QM31.mul q10 q11
  let q12 ← Array.index_usize row.producer_weights 0#usize
  let q13 ← field.QM31.mul q12 q9
  let q14 ← Array.index_usize row.producer_weights 1#usize
  let q15 ← field.QM31.mul q14 q8
  let producer_numerator ← field.QM31.add q13 q15
  let q16 ← Array.index_usize row.consumer_weights 0#usize
  let q17 ← field.QM31.mul q16 q11
  let q18 ← Array.index_usize row.consumer_weights 1#usize
  let q19 ← field.QM31.mul q18 q10
  let consumer_numerator ← field.QM31.add q17 q19
  let q20 ← field.QM31.mul helper consumer_denominator
  let q21 ← field.QM31.add q20 consumer_numerator
  let q22 ← field.QM31.mul producer_denominator q21
  let q23 ← field.QM31.mul consumer_denominator producer_numerator
  field.QM31.sub q22 q23


end FIq_Native
