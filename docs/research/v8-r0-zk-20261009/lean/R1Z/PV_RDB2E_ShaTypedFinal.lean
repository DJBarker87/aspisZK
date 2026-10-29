import R1Z.PV_RDB2E_ShaHandles
namespace R1Z.PV_RDB2E_ShaHandles
open Aeneas Aeneas.Std Result
set_option autoImplicit false

def position (f : Frame) : Usize := UScalar.cast .Usize f.pos
def suffix (f : Frame) : Array U8 8#usize :=
  PV_DL_LengthEncoding.suffix (PV_CBL_ShaBitLength.bitLength (position f) f.core.block_len)
def first (f : Frame) (valid : (position f).val<64) : Array U8 64#usize :=
  ⟨PV_CBL_PaddingModel.first f.buffer.val (position f).val (suffix f).val,
   PV_CBL_PaddingLength.first_length _ _ _ f.buffer.property valid (suffix f).property⟩

def finalize (compress : State → List U8 → Result State) (f : Frame)
    (valid : (position f).val<64) : Result Frame := do
  let after ← PV_DL_CompressionTrace.run compress
    (PV_CBL_PaddingModel.blocks f.buffer.val (position f).val (suffix f).val) f.core.state
  ok ⟨⟨after,f.core.block_len⟩,first f valid,0#u8,PV_DL_ShaSerialize.array after⟩

def forget (f : Frame) : PV_RDB2D_SHAState.Restored :=
  ⟨f.core,f.buffer.val,f.pos.val,f.output.val⟩

theorem complete_typed (compress : State → List U8 → Result State) (f : Frame)
    (valid : (position f).val<64) :
    (do let after ← finalize compress f valid;ok (forget after))=
      PV_RDB2D_SHAState.finalize compress f.core f.buffer (position f) f.output := by
  rw [PV_RDB2D_SHAState.all_mutable_fields compress f.core f.buffer (position f) f.output valid]
  simp only [finalize,forget,first,suffix,PV_RDB2D_SHAState.completeState,bind_assoc_eq,bind_tc_ok]
  rfl

theorem output_length (f : Frame) : f.output.val.length=32 := f.output.property

theorem buffer_length (f : Frame) : f.buffer.val.length=64 := f.buffer.property

#print axioms complete_typed
#print axioms output_length
#print axioms buffer_length
end R1Z.PV_RDB2E_ShaHandles
