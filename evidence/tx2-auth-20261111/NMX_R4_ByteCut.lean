import NMX_R3_RegistryByteCut
import NMX_R2_LaneView
set_option autoImplicit false
noncomputable section
namespace NMX_R4_ByteCut
open Aeneas Aeneas.Std
open NMX_R3_RegistryByteCut (cut bound empty)

theorem master_nil : LIBB_PoolLib.library.decodeMaster [] = none := by
 change NMX_R2_DecoderLibrary.master [] = none
 rfl

theorem checkpoint_nil : LIBB_PoolLib.library.decodeCheckpoint [] = none := by
 change NMX_R2_DecoderLibrary.checkpoint [] = none
 rfl

theorem master (b : RSL.Bytes) :
 LIBB_PoolLib.library.decodeMaster (cut b) = LIBB_PoolLib.library.decodeMaster b := by
 unfold cut
 split
 · rfl
 · rename_i large
   rw [master_nil]
   change none = NMX_R2_DecoderLibrary.master b
   simp only [NMX_R2_DecoderLibrary.master,NMX_R2_InverseSlice.fromBytes,dif_neg large]

theorem checkpoint (b : RSL.Bytes) :
 LIBB_PoolLib.library.decodeCheckpoint (cut b) = LIBB_PoolLib.library.decodeCheckpoint b := by
 unfold cut
 split
 · rfl
 · rename_i large
   rw [checkpoint_nil]
   change none = NMX_R2_DecoderLibrary.checkpoint b
   simp only [NMX_R2_DecoderLibrary.checkpoint,NMX_R2_InverseSlice.fromBytes,dif_neg large]

theorem lane (b : RSL.Bytes) : RSL.TX2_217.Ref (cut b) = RSL.TX2_217.Ref b := by
 unfold cut
 split
 · rfl
 · rename_i large
   have fits : RSL.LANE_ACCOUNT_BYTES ≤ Usize.max := NMX_R2_InverseSliceProps.lane_fits
   have wrong : b.length ≠ RSL.LANE_ACCOUNT_BYTES := by omega
   rw [NMX_R2_LaneView.wrong_length b wrong,NMX_R2_LaneView.wrong_length [] (by decide)]
#print axioms master_nil
#print axioms checkpoint_nil
#print axioms master
#print axioms checkpoint
#print axioms lane
end NMX_R4_ByteCut
end
