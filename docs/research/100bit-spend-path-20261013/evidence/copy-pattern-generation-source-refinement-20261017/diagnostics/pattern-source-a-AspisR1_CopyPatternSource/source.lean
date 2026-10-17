import CopyEndpointSource

/-! Exact indexed-candidate Copy pattern carrier, registry and execution.
The shared lift names its already proved exact endpoint owner. -/
set_option autoImplicit false
namespace AspisR1CopyPatternCandidate
open Aeneas Aeneas.Std Result Error
open AspisR1SelectedMaskProbe

structure pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern
  where
  kinds : Array Std.U8 16#usize
  columns : Array Std.U8 16#usize
  offsets : Array Std.U32 16#usize

@[global_simps, irreducible]
def poseidon2.POSEIDON2_WIDTH : Std.Usize := 16#usize

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

@[global_simps, irreducible]
def
  pool_v1.pair_forest_copy_terminal.POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1
  : Std.Usize :=
  14#usize

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
        let q1 ← AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.lift_m31 i3
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

def pool_v1.pair_forest_copy_terminal.pattern_values
  (openings : Array field.QM31 16#usize) (lambda : field.QM31) :
  Result (Array field.QM31 14#usize)
  := do
  pool_v1.pair_forest_copy_terminal.pattern_values_literal openings lambda

end AspisR1CopyPatternCandidate
