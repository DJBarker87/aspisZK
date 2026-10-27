import F3U_SourceInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_AsSliceBytes
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem byte (b : Byte) : decodeByte (UScalar.ofNatCore b.val b.isLt : U8)=b := by
  apply Fin.ext
  rfl

theorem inverse (bytes : Bytes) (pub : Slice U8) (decoded : Port1_Driver.asSlice bytes=some pub) :
    bytesOf pub.val=bytes := by
  unfold Port1_Driver.asSlice at decoded
  split at decoded
  · have same := Option.some.inj decoded
    subst pub
    simp only [bytesOf,List.map_map]
    induction bytes with
    | nil=>rfl
    | cons b bs ih=>simpa only [List.map_cons,Function.comp_apply,byte] using congrArg (List.cons b) ih
  · cases decoded

#print axioms byte
#print axioms inverse
end AspisR1.F3U_AsSliceBytes
end
