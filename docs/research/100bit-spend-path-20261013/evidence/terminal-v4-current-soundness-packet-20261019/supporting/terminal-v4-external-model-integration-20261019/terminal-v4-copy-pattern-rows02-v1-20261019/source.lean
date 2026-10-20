-- Focused source factoring of the generated COPY_PATTERNS declaration.
import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CopyPatternsSupportV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe

namespace pool_v1.pair_forest_copy_terminal.constants

def copyPattern_07 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
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
      offsets := copyPatternsZeroU32
    }

def copyPattern_08 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
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
      offsets := copyPatternsZeroU32
    }

def copyPattern_09 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
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
      offsets := copyPatternsZeroU32
    }

def copyPattern_10 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
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
    }

def copyPattern_11 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
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
      offsets := copyPatternsZeroU32
    }

def copyPattern_12 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
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
      offsets := copyPatternsZeroU32
    }

def copyPattern_13 : pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestPattern :=
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
      offsets := copyPatternsZeroU32
    }

end pool_v1.pair_forest_copy_terminal.constants
end AspisR1SelectedMaskProbe
