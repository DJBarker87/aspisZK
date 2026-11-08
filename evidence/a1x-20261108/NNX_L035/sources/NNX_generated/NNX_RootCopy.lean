import NNX_FinishPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_RootCopy
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

theorem key (root : Array U8 32#usize) :
 LIB_Env.nativeKey (LIB_Carriers.b32 root) = root := by
 apply Subtype.ext
 exact NNC_ByteCarriers.native_host root.val

theorem source (bytes : Slice U8) (root : RSL.B32)
 (converted : RSL.TX1_136.toB32 (LIB_Carriers.bytes bytes) = some root) :
 core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 bytes =
 .ok (.Ok (LIB_Env.nativeKey root)) := by
 unfold RSL.TX1_136.toB32 at converted
 split at converted
 · rename_i length
   cases Option.some.inj converted
   have rawLength : bytes.val.length=32 := by
    simpa only [LIB_Carriers.bytes,NMS_R2N_RSLScalars.bytes,List.length_map] using length
   unfold core.array.TryFromArrayCopySlice.try_from
   simp only [Slice.length,rawLength,dif_pos]
   apply congrArg (fun r : Array U8 32#usize => Result.ok (core.result.Result.Ok r))
   apply Subtype.ext
   exact (LIB_Carriers.bytes_roundtrip bytes).symm
 · cases converted
#print axioms key
#print axioms source
end AspisR1.NNX_RootCopy
end
