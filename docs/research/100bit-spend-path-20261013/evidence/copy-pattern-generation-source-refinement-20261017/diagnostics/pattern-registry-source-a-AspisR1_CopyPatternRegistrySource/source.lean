import AspisR1SelectedMaskProbe.Funs
import Aeneas.Tactic.RustAttributes

/-! Exact sealed indexed-candidate source partition. -/
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

end AspisR1CopyPatternCandidate
