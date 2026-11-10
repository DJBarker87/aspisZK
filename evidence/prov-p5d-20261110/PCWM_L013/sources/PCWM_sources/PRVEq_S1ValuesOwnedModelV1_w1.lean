-- PCWM_ w1: S1ValuesOwnedModelV1, ReconstructedSource.  The fresh text is the PCWC_E001 emission of the RECONSTRUCTED crate sources/s1_y1_v1 (original Aeneas 959659a6, Charon daad69be,
-- overflow checks ON, nightly-2026-06-01 assumed, NOT the frozen 4bb3b3f toolchain and NOT frozen source: the reference is a hand-written owned-buffer model of compact::expand_values).
-- Label: ReconstructedSource, not frozen-equal.  Statements are against the gate constants of S1ValuesOwnedModelV1.
import Aeneas
import S1ValuesOwnedModelV1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace AspisS1ValuesOwned
namespace PRVFresh_S1ValuesOwnedModelV1_w1
/-- [aspis_s1_y1_source_20261024::CodecError]
    Source: 'src/lib.rs', lines 7:0-11:1
    Visibility: public -/
inductive CodecError where
| Length : CodecError
| NonZeroHigh : CodecError
| NonCanonical : CodecError

/-- [aspis_s1_y1_source_20261024::read_input]:
    Source: 'src/lib.rs', lines 31:0-34:1
    Visibility: public -/
def read_input
  (input : alloc.vec.Vec Std.U8) (index : Std.Usize) :
  Result (Std.U8 × (alloc.vec.Vec Std.U8))
  := do
  let value ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Std.U8) input
      index
  ok (value, input)

/-- [aspis_s1_y1_source_20261024::write_output]:
    Source: 'src/lib.rs', lines 36:0-39:1
    Visibility: public -/
def write_output
  (output : alloc.vec.Vec Std.U8) (index : Std.Usize) (value : Std.U8) :
  Result (alloc.vec.Vec Std.U8)
  := do
  let (_, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Std.U8)
      output index
  ok (index_mut_back value)

/-- [aspis_s1_y1_source_20261024::copy_chunk]: loop body 0:
    Source: 'src/lib.rs', lines 42:4-48:5
    Visibility: public -/
def copy_chunk_loop.body
  (chunk : Std.Usize) (input : alloc.vec.Vec Std.U8)
  (output : alloc.vec.Vec Std.U8) (byte : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8) ×
    Std.Usize) ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8)))
  := do
  if byte < 16#usize
  then
    let i ← chunk * 16#usize
    let i1 ← i + byte
    let (value, next) ← read_input input i1
    let i2 ← chunk * 32#usize
    let i3 ← i2 + byte
    let output1 ← write_output output i3 value
    let i4 ← i2 + 16#usize
    let i5 ← i4 + byte
    let output2 ← write_output output1 i5 0#u8
    let byte1 ← byte + 1#usize
    ok (cont (next, output2, byte1))
  else ok (done (input, output))

/-- [aspis_s1_y1_source_20261024::copy_chunk]: loop 0:
    Source: 'src/lib.rs', lines 42:4-48:5
    Visibility: public -/
def copy_chunk_loop
  (input : alloc.vec.Vec Std.U8) (output : alloc.vec.Vec Std.U8)
  (chunk : Std.Usize) (byte : Std.Usize) :
  Result ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8))
  := do
  loop
    (fun (input1, output1, byte1) => copy_chunk_loop.body chunk input1 output1
      byte1)
    (input, output, byte)

/-- [aspis_s1_y1_source_20261024::copy_chunk]:
    Source: 'src/lib.rs', lines 40:0-50:1
    Visibility: public -/
@[reducible]
def copy_chunk
  (input : alloc.vec.Vec Std.U8) (output : alloc.vec.Vec Std.U8)
  (chunk : Std.Usize) :
  Result ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8))
  := do
  copy_chunk_loop input output chunk 0#usize

/-- [aspis_s1_y1_source_20261024::values_owned_reference]: loop body 0:
    Source: 'src/lib.rs', lines 59:4-64:5
    Visibility: public -/
def values_owned_reference_loop.body
  (count : Std.Usize) (input : alloc.vec.Vec Std.U8)
  (output : alloc.vec.Vec Std.U8) (chunk : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8) ×
    Std.Usize) ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8)))
  := do
  if chunk < count
  then
    let (next_input, next_output) ← copy_chunk input output chunk
    let chunk1 ← chunk + 1#usize
    ok (cont (next_input, next_output, chunk1))
  else ok (done (input, output))

/-- [aspis_s1_y1_source_20261024::values_owned_reference]: loop 0:
    Source: 'src/lib.rs', lines 59:4-64:5
    Visibility: public -/
def values_owned_reference_loop
  (input : alloc.vec.Vec Std.U8) (output : alloc.vec.Vec Std.U8)
  (count : Std.Usize) (chunk : Std.Usize) :
  Result ((alloc.vec.Vec Std.U8) × (alloc.vec.Vec Std.U8))
  := do
  loop
    (fun (input1, output1, chunk1) => values_owned_reference_loop.body count
      input1 output1 chunk1)
    (input, output, chunk)

/-- [aspis_s1_y1_source_20261024::values_owned_reference]:
    Source: 'src/lib.rs', lines 53:0-66:1
    Visibility: public -/
def values_owned_reference
  (input : alloc.vec.Vec Std.U8) (output : alloc.vec.Vec Std.U8) :
  Result ((core.result.Result Unit CodecError) × (alloc.vec.Vec Std.U8) ×
    (alloc.vec.Vec Std.U8))
  := do
  let i := alloc.vec.Vec.len input
  let i1 ← i % 16#usize
  if i1 != 0#usize
  then ok (core.result.Result.Err CodecError.Length, input, output)
  else
    let i2 := alloc.vec.Vec.len output
    let i3 := alloc.vec.Vec.len input
    let i4 ← 2#usize * i3
    if i2 != i4
    then ok (core.result.Result.Err CodecError.Length, input, output)
    else
      let i5 := alloc.vec.Vec.len input
      let count ← i5 / 16#usize
      let (input1, output1) ←
        values_owned_reference_loop input output count 0#usize
      ok (core.result.Result.Ok (), input1, output1)


end PRVFresh_S1ValuesOwnedModelV1_w1
end AspisS1ValuesOwned

namespace PRVEq.S1ValuesOwnedModelV1_w1
open AspisS1ValuesOwned

theorem read_input : @AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.read_input = @AspisS1ValuesOwned.read_input := by
  rfl
#print axioms read_input

theorem write_output : @AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.write_output = @AspisS1ValuesOwned.write_output := by
  rfl
#print axioms write_output

theorem copy_chunk_loop.body : @AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.copy_chunk_loop.body = @AspisS1ValuesOwned.copy_chunk_loop.body := by
  rfl
#print axioms copy_chunk_loop.body

theorem copy_chunk_loop : @AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.copy_chunk_loop = @AspisS1ValuesOwned.copy_chunk_loop := by
  rfl
#print axioms copy_chunk_loop

theorem copy_chunk : @AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.copy_chunk = @AspisS1ValuesOwned.copy_chunk := by
  rfl
#print axioms copy_chunk

theorem values_owned_reference_loop.body : @AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.values_owned_reference_loop.body = @AspisS1ValuesOwned.values_owned_reference_loop.body := by
  rfl
#print axioms values_owned_reference_loop.body

theorem values_owned_reference_loop : @AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.values_owned_reference_loop = @AspisS1ValuesOwned.values_owned_reference_loop := by
  rfl
#print axioms values_owned_reference_loop

/-- the local enum of the reconstructed crate maps to the frozen compact.CodecError constructor by constructor (the gate's carrier) -/
def toFrozen : AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.CodecError → AspisS1ValuesOwned.CodecError
  | .Length => .Length
  | .NonZeroHigh => .NonZeroHigh
  | .NonCanonical => .NonCanonical

def mapRes : core.result.Result Unit AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.CodecError → core.result.Result Unit AspisS1ValuesOwned.CodecError
  | .Ok u => .Ok u
  | .Err e => .Err (toFrozen e)

/-- values_owned_reference: gate = fresh with the error carrier mapped (the only function whose type mentions the local enum) -/
theorem values_owned_reference (input output : alloc.vec.Vec Std.U8) :
    (AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.values_owned_reference input output >>= fun x => ok (mapRes x.1, x.2.1, x.2.2)) = AspisS1ValuesOwned.values_owned_reference input output := by
  unfold AspisS1ValuesOwned.PRVFresh_S1ValuesOwnedModelV1_w1.values_owned_reference AspisS1ValuesOwned.values_owned_reference
  split <;> simp_all [mapRes, toFrozen]
  all_goals first | rfl | skip
#print axioms values_owned_reference

end PRVEq.S1ValuesOwnedModelV1_w1
