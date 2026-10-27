import PoolS2_PrefixSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_InstructionSource
open Aeneas Aeneas.Std Result

def magic : Result (Array U8 4#usize) := ok (Array.make 4#usize [65#u8,83#u8,56#u8,67#u8])
def laneCount : Result Usize := ok 8#usize
def instructionVersion : Result U8 := ok 1#u8
def digestVersion : Result U8 := ok 1#u8
/-- Documented pure std slice/array inequality, on complete original bytes. -/
def sliceNe {N : Usize} (bytes : Slice U8) (image : Array U8 N) : Result Bool := by
  classical
  exact ok (decide (bytes.val ≠ image.val))

def pair_forest.encode_pair_forest_checkpoint_instruction_v1
  : Result (Array Std.U8 8#usize) := do
  let a ← magic
  let i ← Array.index_usize a 0#usize
  let i1 ← Array.index_usize a 1#usize
  let i2 ← Array.index_usize a 2#usize
  let i3 ← Array.index_usize a 3#usize
  let i4 ←
    laneCount
  let i5 ← lift (UScalar.cast .U8 i4)
  let i6 ← instructionVersion
  let i7 ← digestVersion
  ok (Array.make 8#usize [ i, i1, i2, i3, i6, i5, i7, 0#u8 ])

/-- [aspis_pool::pair_forest::decode_pair_forest_checkpoint_instruction_v1]:
    Source: 'programs/aspis-pool/src/pair_forest.rs', lines 272:0-277:1
    Visibility: public -/
def pair_forest.decode_pair_forest_checkpoint_instruction_v1
  (bytes : Slice Std.U8) :
  Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)
  := do
  let a ← pair_forest.encode_pair_forest_checkpoint_instruction_v1
  let b ←
    sliceNe bytes a
  if b
  then
    ok (core.result.Result.Err
      AdapterRw.solana_program_error.ProgramError.InvalidInstructionData)
  else ok (core.result.Result.Ok ())


#print axioms pair_forest.encode_pair_forest_checkpoint_instruction_v1
#print axioms pair_forest.decode_pair_forest_checkpoint_instruction_v1
end AspisR1.PoolS2_InstructionSource
end
