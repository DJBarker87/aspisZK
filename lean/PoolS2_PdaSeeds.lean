import PoolS2_PdaSource
set_option autoImplicit false
namespace AspisR1.PoolS2_PdaSeeds
open Aeneas Aeneas.Std Result PoolS2_PdaSource
def masterPrefix : Slice U8 := ⟨[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,109#u8,97#u8,115#u8,116#u8,101#u8,114#u8,45#u8,118#u8,49#u8],by scalar_tac⟩
def lanePrefix : Slice U8 := ⟨[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,108#u8,97#u8,110#u8,101#u8,45#u8,118#u8,49#u8],by scalar_tac⟩
def checkpointPrefix : Slice U8 := ⟨[97#u8,115#u8,112#u8,105#u8,115#u8,45#u8,112#u8,97#u8,105#u8,114#u8,45#u8,102#u8,111#u8,114#u8,101#u8,115#u8,116#u8,45#u8,99#u8,104#u8,101#u8,99#u8,107#u8,112#u8,111#u8,105#u8,110#u8,116#u8,45#u8,118#u8,49#u8],by scalar_tac⟩

def keyBytes (key : Key) : Slice U8 := Array.to_slice key
def oneByte (b : U8) : Slice U8 := Array.to_slice (Array.make 1#usize [b])
def sequenceBytes (seq : U64) : Slice U8 := Array.to_slice (core.num.U64.to_le_bytes seq)
def masterFind (mint : Key) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize [masterPrefix,keyBytes mint])
def masterCreate (mint : Key) (bump : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [masterPrefix,keyBytes mint,oneByte bump])
def laneFind (master : Key) (lane : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [lanePrefix,keyBytes master,oneByte lane])
def laneCreate (master : Key) (lane bump : U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 4#usize [lanePrefix,keyBytes master,oneByte lane,oneByte bump])
def checkpointFind (master : Key) (seq : U64) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [checkpointPrefix,keyBytes master,sequenceBytes seq])

theorem master_prefix : masterSeed = ok masterPrefix := rfl
theorem lane_prefix : laneSeed = ok lanePrefix := rfl
theorem checkpoint_prefix : checkpointSeed = ok checkpointPrefix := rfl
theorem key_bytes (key : Key) : (keyBytes key).val = key.val := rfl
theorem one_byte (b : U8) : (oneByte b).val = [b] := rfl
theorem sequence_bytes (seq : U64) :
    (sequenceBytes seq).val = (core.num.U64.to_le_bytes seq).val := rfl

#print axioms master_prefix
#print axioms lane_prefix
#print axioms checkpoint_prefix
#print axioms key_bytes
#print axioms one_byte
#print axioms sequence_bytes
end AspisR1.PoolS2_PdaSeeds
