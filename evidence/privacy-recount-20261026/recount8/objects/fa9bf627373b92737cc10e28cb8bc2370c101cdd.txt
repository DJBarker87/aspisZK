import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace R1Z.ProverRwDictionaryLayoutSource

-- Literal retained emitted declaration bodies; no external template imported.
def compact.FINAL_LEN : Std.Usize := 64#usize

def compact.HEADER : Std.Usize := 16#usize

def compact.OFF_SEMANTIC : Std.Usize := compact.HEADER

def compact.SEMANTIC_COMPACT_VALUES : Result Std.Usize := do
  let i ← 10#usize * 28#usize
  let i1 ← 1#usize + i
  let i2 ← 87#usize + 29#usize
  let i3 ← i1 + i2
  i3 + 29#usize

def verifier.SEMANTIC_BYTES : Result Std.Usize := do
  let i ← 29#usize * 32#usize
  12903#usize + i

def compact.LOGICAL_SEMANTIC : Result Std.Usize := verifier.SEMANTIC_BYTES

def compact.COMPACT_SEMANTIC : Result Std.Usize := do
  let i ← compact.SEMANTIC_COMPACT_VALUES
  let i1 ← 16#usize * i
  let i2 ← compact.LOGICAL_SEMANTIC
  i2 - i1

def compact.OFF_Y1 : Result Std.Usize := do
  let i ← compact.COMPACT_SEMANTIC
  compact.OFF_SEMANTIC + i

def compact.COMPACT_Y1 : Result Std.Usize := 29#usize * 16#usize

def compact.OFF_INACTIVE : Result Std.Usize := do
  let i ← compact.OFF_Y1
  let i1 ← compact.COMPACT_Y1
  i + i1

def compact.OFF_ROUND0 : Result Std.Usize := do
  let i ← compact.OFF_INACTIVE
  i + 32#usize

def compact.OFF_FOLDED_ROOT : Result Std.Usize := do
  let i ← compact.OFF_ROUND0
  i + 224#usize

def compact.OFF_ROUND1 : Result Std.Usize := do
  let i ← compact.OFF_FOLDED_ROOT
  i + 32#usize

def compact.OFF_FINAL : Result Std.Usize := do
  let i ← compact.OFF_ROUND1
  i + 224#usize

def compact.OFF_OPENINGS : Result Std.Usize := do
  let i ← compact.FINAL_LEN * 32#usize
  let i1 ← compact.OFF_FINAL
  i1 + i

def compact.OPENING : Result Std.Usize := do
  let i ← 480#usize + 128#usize
  let i1 ← i + 32#usize
  let i2 ← i1 + 32#usize
  let i3 ← i2 + 128#usize
  i3 + 32#usize

def compact.QUERIES : Std.Usize := 22#usize

def compact.OFF_NODES : Result Std.Usize := do
  let i ← compact.OPENING
  let i1 ← compact.QUERIES * i
  let i2 ← compact.OFF_OPENINGS
  i2 + i1

def compact.MAX_NODES : Result Std.Usize := do
  let i ← 146#usize + 172#usize
  let i1 ← 2#usize * i
  let i2 ← 128#usize + 150#usize
  i1 + i2

def compact.FIXED : Result Std.Usize := compact.OFF_NODES

def compact.MAX_PROOF : Result Std.Usize := do
  let i ← compact.MAX_NODES
  let i1 ← 32#usize * i
  let i2 ← compact.FIXED
  i2 + i1

def compact.PROOF_BYTES : Result Std.Usize := compact.MAX_PROOF

def compact.MAGIC : Array Std.U8 8#usize :=
  Array.make 8#usize [ 82#u8, 49#u8, 80#u8, 51#u8, 67#u8, 66#u8, 49#u8, 56#u8 ]

def compact.SLOT_NODES : Array Std.Usize 6#usize :=
  Array.make 6#usize [
    146#usize, 146#usize, 128#usize, 172#usize, 172#usize, 150#usize
    ]

end R1Z.ProverRwDictionaryLayoutSource
