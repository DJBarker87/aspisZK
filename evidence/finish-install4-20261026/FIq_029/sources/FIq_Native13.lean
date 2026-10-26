import FIq_Native12
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::constants::COPY_PATTERNS]
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal_constants.rs', lines 10:0-25:2 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS
  :
  Array pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern
    14#usize
  :=
  let a := Array.repeat 16#usize 1#u8
  let a1 := Array.repeat 16#usize 0#u32
  let a2 := Array.repeat 16#usize 0#u32
  let a3 := Array.repeat 16#usize 0#u32
  let a4 := Array.repeat 16#usize 0#u32
  let a5 := Array.repeat 16#usize 0#u32
  let a6 := Array.repeat 16#usize 0#u32
  let a7 := Array.repeat 16#usize 0#u8
  let a8 := Array.repeat 16#usize 0#u32
  let a9 := Array.repeat 16#usize 0#u32
  let a10 := Array.repeat 16#usize 0#u32
  let a11 := Array.repeat 16#usize 0#u32
  let a12 := Array.repeat 16#usize 0#u32
  let a13 := Array.repeat 16#usize 0#u32
  let a14 := Array.repeat 16#usize 0#u32
  Array.make 14#usize [
    {
      kinds := a,
      columns :=
        (Array.make 16#usize [
          0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 9#u8, 10#u8,
          11#u8, 12#u8, 13#u8, 14#u8, 15#u8
          ]),
      offsets := a1
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a2
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a3
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a4
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          0#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a5
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          6#u8, 7#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a6
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns := a7,
      offsets := a8
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          10#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a9
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a10
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          2#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a11
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          8#u8, 9#u8, 10#u8, 11#u8, 12#u8, 13#u8, 14#u8, 15#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets :=
        (Array.make 16#usize [
          0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 1051521018#u32,
          0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32, 0#u32
          ])
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 9#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a12
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a13
    },
    {
      kinds :=
        (Array.make 16#usize [
          1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 1#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns :=
        (Array.make 16#usize [
          8#u8, 9#u8, 10#u8, 11#u8, 12#u8, 13#u8, 14#u8, 15#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      offsets := a14
    }
    ]

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1]
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 19:0-19:68
    Visibility: public -/
@[global_simps, irreducible]
def
  pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1
  : Std.Usize :=
  14#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::pattern_values_literal]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 254:4-258:5 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0
  (lambda : field.QM31) (powers : Array field.QM31 16#usize)
  (power : field.QM31) (limb : Std.Usize) :
  Result ((Array field.QM31 16#usize) × Std.Usize)
  := do
  if limb < poseidon2.POSEIDON2_WIDTH
  then
    let a ← Array.update powers limb power
    let power1 ← field.QM31.mul power lambda
    let limb1 ← limb + 1#usize
    pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0 lambda a
      power1 limb1
  else ok (powers, limb)
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::pattern_values_literal]: loop 2:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 265:8-272:9 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0
  (openings : Array field.QM31 16#usize) (powers : Array field.QM31 16#usize)
  (limb : Std.Usize)
  (pattern : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern)
  (value : field.QM31) :
  Result (Std.Usize × field.QM31)
  := do
  if limb < poseidon2.POSEIDON2_WIDTH
  then
    let i ← Array.index_usize pattern.kinds limb
    let value1 ←
      if i = 1#u8
      then
        do
        let i1 ← Array.index_usize pattern.columns limb
        let i2 ← lift (core.convert.num.FromUsizeU8.from i1)
        let q ← Array.index_usize openings i2
        let i3 ← Array.index_usize pattern.offsets limb
        let q1 ← pool_v1.pair_forest_copy_terminal.lift_m31 i3
        let source ← field.QM31.add q q1
        let q2 ← Array.index_usize powers limb
        let q3 ← field.QM31.mul q2 source
        field.QM31.add value q3
      else ok value
    let limb1 ← limb + 1#usize
    pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0
      openings powers limb1 pattern value1
  else ok (limb, value)
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::pattern_values_literal]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 261:4-275:5 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1
  (openings : Array field.QM31 16#usize) (powers : Array field.QM31 16#usize)
  (limb : Std.Usize) (result : Array field.QM31 14#usize)
  (pattern_index : Std.Usize) :
  Result (Array field.QM31 14#usize)
  := do
  if pattern_index <
    pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1
  then
    let pattern ←
      Array.index_usize
        pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS pattern_index
    let (limb1, value) ←
      pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1_loop0
        openings powers 0#usize pattern field.QM31.ZERO
    let a ← Array.update result pattern_index value
    let pattern_index1 ← pattern_index + 1#usize
    pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1 openings
      powers limb1 a pattern_index1
  else ok result
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::pattern_values_literal]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 247:0-277:1 -/
def pool_v1.pair_forest_copy_terminal.pattern_values_literal
  (openings : Array field.QM31 16#usize) (lambda : field.QM31) :
  Result (Array field.QM31 14#usize)
  := do
  let powers := Array.repeat 16#usize field.QM31.ZERO
  let (powers1, limb) ←
    pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0 lambda
      powers lambda 0#usize
  let result := Array.repeat 14#usize field.QM31.ZERO
  pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1 openings
    powers1 limb result 0#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::pattern_values]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 335:0-343:1 -/
def pool_v1.pair_forest_copy_terminal.pattern_values
  (openings : Array field.QM31 16#usize) (lambda : field.QM31) :
  Result (Array field.QM31 14#usize)
  := do
  pool_v1.pair_forest_copy_terminal.pattern_values_literal openings lambda

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::constants::ACTIVE_ROW_MASKS]
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal_constants.rs', lines 5:0-5:438 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS
  : Array Std.U16 64#usize :=
  Array.make 64#usize [
    6144#u16, 6144#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6144#u16, 4097#u16, 2048#u16,
    6145#u16, 2049#u16, 2048#u16, 6145#u16, 2049#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 4097#u16, 6145#u16, 6145#u16,
    4097#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16,
    1749#u16
    ]

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::selector_mask_sum_16]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 125:4-133:5 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop
  (values : Array field.QM31 16#usize) (mask : Std.U16) (complement : Bool)
  (sum : field.QM31) :
  Result field.QM31
  := do
  if mask != 0#u16
  then
    let i ← core.num.U16.trailing_zeros mask
    let index ← lift (UScalar.cast .Usize i)
    let sum1 ←
      if complement
      then do
           let q ← Array.index_usize values index
           field.QM31.sub sum q
      else do
           let q ← Array.index_usize values index
           field.QM31.add sum q
    let i1 ← mask - 1#u16
    let mask1 ← lift (mask &&& i1)
    pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop values mask1
      complement sum1
  else ok sum
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::selector_mask_sum_16]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 119:0-135:1 -/
def pool_v1.pair_forest_copy_terminal.selector_mask_sum_16
  (values : Array field.QM31 16#usize) (mask : Std.U16) :
  Result field.QM31
  := do
  let i ← core.num.U16.count_ones mask
  let (mask1, complement) ←
    if i > 8#u32
    then do
         let mask2 ← lift (~~~ mask)
         ok (mask2, true)
    else ok (mask, false)
  let sum ← if complement
              then ok field.QM31.ONE
              else ok field.QM31.ZERO
  pool_v1.pair_forest_copy_terminal.selector_mask_sum_16_loop values mask1
    complement sum

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_literal]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 183:8-189:9 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop
  (self : pool_v1.pair_forest_copy_terminal.Selectors) (sum : field.QM31)
  (block : Std.Usize) :
  Result field.QM31
  := do
  if block < 64#usize
  then
    let mask ←
      Array.index_usize
        pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS block
    let (self1, sum1) ←
      if mask != 0#u16
      then
        do
        let q ← Array.index_usize self.high block
        let q1 ←
          pool_v1.pair_forest_copy_terminal.selector_mask_sum_16 self.low mask
        let q2 ← field.QM31.mul q q1
        let sum2 ← field.QM31.add sum q2
        ok (self, sum2)
      else ok (self, sum)
    let block1 ← block + 1#usize
    pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop self1 sum1
      block1
  else ok sum
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_literal]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 180:4-191:5 -/
@[reducible]
def pool_v1.pair_forest_copy_terminal.Selectors.active_literal
  (self : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result field.QM31
  := do
  pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop self
    field.QM31.ZERO 0#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 238:4-243:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.active
  (self : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result field.QM31
  := do
  pool_v1.pair_forest_copy_terminal.Selectors.active_literal self


end FIq_Native
