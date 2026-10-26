import PoolS2_InstructionSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_Instruction
open Aeneas Aeneas.Std Result PoolS2_InstructionSource

def wire : List U8 := [65#u8,83#u8,56#u8,67#u8,1#u8,8#u8,1#u8,0#u8]

theorem encoded : pair_forest.encode_pair_forest_checkpoint_instruction_v1 =
    ok (Array.make 8#usize wire) := by
  rfl

theorem accepted (bytes : Slice U8) :
    pair_forest.decode_pair_forest_checkpoint_instruction_v1 bytes = ok (.Ok ()) ↔
      bytes.val = wire := by
  classical
  rw [pair_forest.decode_pair_forest_checkpoint_instruction_v1,encoded]
  simp [sliceNe]

theorem wrong_length (bytes : Slice U8) (different : bytes.val.length ≠ 8) :
    pair_forest.decode_pair_forest_checkpoint_instruction_v1 bytes =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData) := by
  classical
  have ne : bytes.val ≠ wire := by
    intro h
    apply different
    simpa [wire] using congrArg List.length h
  rw [pair_forest.decode_pair_forest_checkpoint_instruction_v1,encoded]
  simp [sliceNe,ne]

#print axioms encoded
#print axioms accepted
#print axioms wrong_length
end AspisR1.PoolS2_Instruction
end
