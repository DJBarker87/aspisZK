import TerminalV4CopyPatternsRows01V1
import TerminalV4CopyPatternsRows02V1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
namespace pool_v1.pair_forest_copy_terminal.constants

def sourceRecord_00 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  let a := Array.repeat 16#usize 1#u8;
  let a1 := Array.repeat 16#usize 0#u32;
  let a2 := Array.repeat 16#usize 0#u32;
  let a3 := Array.repeat 16#usize 0#u32;
  let a4 := Array.repeat 16#usize 0#u32;
  let a5 := Array.repeat 16#usize 0#u32;
  let a6 := Array.repeat 16#usize 0#u32;
  let a7 := Array.repeat 16#usize 0#u8;
  let a8 := Array.repeat 16#usize 0#u32;
  let a9 := Array.repeat 16#usize 0#u32;
  let a10 := Array.repeat 16#usize 0#u32;
  let a11 := Array.repeat 16#usize 0#u32;
  let a12 := Array.repeat 16#usize 0#u32;
  let a13 := Array.repeat 16#usize 0#u32;
  let a14 := Array.repeat 16#usize 0#u32;
      {
      kinds := a,
      columns :=
        (Array.make 16#usize [
          0#u8, 1#u8, 2#u8, 3#u8, 4#u8, 5#u8, 6#u8, 7#u8, 8#u8, 9#u8, 10#u8,
          11#u8, 12#u8, 13#u8, 14#u8, 15#u8
          ]),
      offsets := a1
    }

theorem sourceRecord_00_eq_factored : sourceRecord_00 = copyPattern_00 := by rfl

def sourceRecord_01 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  let a := Array.repeat 16#usize 1#u8;
  let a1 := Array.repeat 16#usize 0#u32;
  let a2 := Array.repeat 16#usize 0#u32;
  let a3 := Array.repeat 16#usize 0#u32;
  let a4 := Array.repeat 16#usize 0#u32;
  let a5 := Array.repeat 16#usize 0#u32;
  let a6 := Array.repeat 16#usize 0#u32;
  let a7 := Array.repeat 16#usize 0#u8;
  let a8 := Array.repeat 16#usize 0#u32;
  let a9 := Array.repeat 16#usize 0#u32;
  let a10 := Array.repeat 16#usize 0#u32;
  let a11 := Array.repeat 16#usize 0#u32;
  let a12 := Array.repeat 16#usize 0#u32;
  let a13 := Array.repeat 16#usize 0#u32;
  let a14 := Array.repeat 16#usize 0#u32;
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
    }

theorem sourceRecord_01_eq_factored : sourceRecord_01 = copyPattern_01 := by rfl

def sourceRecord_02 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  let a := Array.repeat 16#usize 1#u8;
  let a1 := Array.repeat 16#usize 0#u32;
  let a2 := Array.repeat 16#usize 0#u32;
  let a3 := Array.repeat 16#usize 0#u32;
  let a4 := Array.repeat 16#usize 0#u32;
  let a5 := Array.repeat 16#usize 0#u32;
  let a6 := Array.repeat 16#usize 0#u32;
  let a7 := Array.repeat 16#usize 0#u8;
  let a8 := Array.repeat 16#usize 0#u32;
  let a9 := Array.repeat 16#usize 0#u32;
  let a10 := Array.repeat 16#usize 0#u32;
  let a11 := Array.repeat 16#usize 0#u32;
  let a12 := Array.repeat 16#usize 0#u32;
  let a13 := Array.repeat 16#usize 0#u32;
  let a14 := Array.repeat 16#usize 0#u32;
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
    }

theorem sourceRecord_02_eq_factored : sourceRecord_02 = copyPattern_02 := by rfl

def sourceRecord_03 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  let a := Array.repeat 16#usize 1#u8;
  let a1 := Array.repeat 16#usize 0#u32;
  let a2 := Array.repeat 16#usize 0#u32;
  let a3 := Array.repeat 16#usize 0#u32;
  let a4 := Array.repeat 16#usize 0#u32;
  let a5 := Array.repeat 16#usize 0#u32;
  let a6 := Array.repeat 16#usize 0#u32;
  let a7 := Array.repeat 16#usize 0#u8;
  let a8 := Array.repeat 16#usize 0#u32;
  let a9 := Array.repeat 16#usize 0#u32;
  let a10 := Array.repeat 16#usize 0#u32;
  let a11 := Array.repeat 16#usize 0#u32;
  let a12 := Array.repeat 16#usize 0#u32;
  let a13 := Array.repeat 16#usize 0#u32;
  let a14 := Array.repeat 16#usize 0#u32;
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
    }

theorem sourceRecord_03_eq_factored : sourceRecord_03 = copyPattern_03 := by rfl

def sourceRecord_04 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  let a := Array.repeat 16#usize 1#u8;
  let a1 := Array.repeat 16#usize 0#u32;
  let a2 := Array.repeat 16#usize 0#u32;
  let a3 := Array.repeat 16#usize 0#u32;
  let a4 := Array.repeat 16#usize 0#u32;
  let a5 := Array.repeat 16#usize 0#u32;
  let a6 := Array.repeat 16#usize 0#u32;
  let a7 := Array.repeat 16#usize 0#u8;
  let a8 := Array.repeat 16#usize 0#u32;
  let a9 := Array.repeat 16#usize 0#u32;
  let a10 := Array.repeat 16#usize 0#u32;
  let a11 := Array.repeat 16#usize 0#u32;
  let a12 := Array.repeat 16#usize 0#u32;
  let a13 := Array.repeat 16#usize 0#u32;
  let a14 := Array.repeat 16#usize 0#u32;
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
    }

theorem sourceRecord_04_eq_factored : sourceRecord_04 = copyPattern_04 := by rfl

def sourceRecord_05 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  let a := Array.repeat 16#usize 1#u8;
  let a1 := Array.repeat 16#usize 0#u32;
  let a2 := Array.repeat 16#usize 0#u32;
  let a3 := Array.repeat 16#usize 0#u32;
  let a4 := Array.repeat 16#usize 0#u32;
  let a5 := Array.repeat 16#usize 0#u32;
  let a6 := Array.repeat 16#usize 0#u32;
  let a7 := Array.repeat 16#usize 0#u8;
  let a8 := Array.repeat 16#usize 0#u32;
  let a9 := Array.repeat 16#usize 0#u32;
  let a10 := Array.repeat 16#usize 0#u32;
  let a11 := Array.repeat 16#usize 0#u32;
  let a12 := Array.repeat 16#usize 0#u32;
  let a13 := Array.repeat 16#usize 0#u32;
  let a14 := Array.repeat 16#usize 0#u32;
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
    }

theorem sourceRecord_05_eq_factored : sourceRecord_05 = copyPattern_05 := by rfl

def sourceRecord_06 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
  let a := Array.repeat 16#usize 1#u8;
  let a1 := Array.repeat 16#usize 0#u32;
  let a2 := Array.repeat 16#usize 0#u32;
  let a3 := Array.repeat 16#usize 0#u32;
  let a4 := Array.repeat 16#usize 0#u32;
  let a5 := Array.repeat 16#usize 0#u32;
  let a6 := Array.repeat 16#usize 0#u32;
  let a7 := Array.repeat 16#usize 0#u8;
  let a8 := Array.repeat 16#usize 0#u32;
  let a9 := Array.repeat 16#usize 0#u32;
  let a10 := Array.repeat 16#usize 0#u32;
  let a11 := Array.repeat 16#usize 0#u32;
  let a12 := Array.repeat 16#usize 0#u32;
  let a13 := Array.repeat 16#usize 0#u32;
  let a14 := Array.repeat 16#usize 0#u32;
      {
      kinds :=
        (Array.make 16#usize [
          1#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
          0#u8, 0#u8, 0#u8, 0#u8, 0#u8
          ]),
      columns := a7,
      offsets := a8
    }

theorem sourceRecord_06_eq_factored : sourceRecord_06 = copyPattern_06 := by rfl

end pool_v1.pair_forest_copy_terminal.constants
end AspisR1SelectedMaskProbe
