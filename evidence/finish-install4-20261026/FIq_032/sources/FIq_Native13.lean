import FIq_CopyPatterns
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
noncomputable section
namespace FIq_Native

@[global_simps, irreducible]
def pool_v1.pair_forest_copy_terminal.constants.COPY_PATTERNS :
    Array pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern 14#usize :=
  Array.make 14#usize [pattern00,pattern01,pattern02,pattern03,pattern04,pattern05,pattern06,pattern07,pattern08,pattern09,pattern10,pattern11,pattern12,pattern13]

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
