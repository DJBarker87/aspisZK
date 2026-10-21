import Stage2ContinuationTypes
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
/-! Verbatim emitted leaf bodies, without generator attributes/options.
Source locations and body hashes: overflow-freedom-s2 packet/body-pins.json.
This module does not import the unavailable FunsExternal backend. -/
namespace AspisR1Stage2

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

def verifier.candidate.opening
  (proof : Slice Std.U8) (i : Std.Usize) : Result (Slice Std.U8) := do
  let i1 ← compact.OPENING
  let i2 ← i * i1
  let i3 ← compact.OFF_OPENINGS
  let at1 ← i3 + i2
  let i4 ← at1 + i1
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
    Std.U8) proof { start := at1, «end» := i4 }

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

def multiproof.value_at
  (values : Array (Array Std.U8 32#usize) 16#usize) (index : Std.Usize) :
  Result (Array Std.U8 32#usize)
  := do
  Array.index_usize values index

def multiproof.index_at
  (indices : Array Std.U32 16#usize) (index : Std.Usize) : Result Std.U32 := do
  Array.index_usize indices index

def multiproof.LEAF_BITS : Std.U32 := 18#u32

def multiproof.Arity.bits (self : multiproof.Arity) : Result Std.U32 := do
  match self with
  | multiproof.Arity.Two => ok 1#u32
  | multiproof.Arity.Eight => ok 3#u32

def multiproof.Arity.levels (self : multiproof.Arity) : Result Std.U32 := do
  let i ← multiproof.Arity.bits self
  multiproof.LEAF_BITS / i

def multiproof.Arity.width (self : multiproof.Arity) : Result Std.Usize := do
  let i ← multiproof.Arity.bits self
  1#usize <<< i

def verifier.Reader.raw
  (N : Std.Usize) (self : verifier.Reader) :
  Result ((Array Std.U8 N) × verifier.Reader)
  := do
  let i ← self.«at» + N
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) self.bytes { start := self.«at», «end» := i }
  let r ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s
  let b ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  ok (b, { self with «at» := i })

def verifier.CHECKPOINT_FIXED : Result Std.Usize := do
  let i ← 32#usize * 3#usize
  let i1 ← 16#usize + i
  let i2 ← i1 + 64#usize
  let i3 ← 32#usize * 4#usize
  let i4 ← i2 + i3
  let i5 ← i4 + 16#usize
  let i6 ← i5 + 88#usize
  let i7 ← i6 + 160#usize
  let i8 ← i7 + 64#usize
  let i9 ← 32#usize * 2#usize
  let i10 ← i8 + i9
  let i11 ← i10 + 16#usize
  i11 + 32#usize

end AspisR1Stage2
