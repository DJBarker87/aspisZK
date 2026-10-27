import RPz7_F3T_ByteCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_Slice
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

theorem decode_encode (b : U8) : (UScalar.ofNatCore (decodeByte b).val (decodeByte b).isLt : U8)=b := by
  apply UScalar.eq_of_val_eq
  rfl

theorem roundtrip (s : Slice U8) : Port1_Driver.asSlice (bytesOf s.val)=some s := by
  have bound : (bytesOf s.val).length≤Usize.max := by simpa only [bytesOf,List.length_map] using s.property
  unfold Port1_Driver.asSlice
  rw [dif_pos bound]
  simp only [bytesOf,List.map_map]
  have words : s.val.map (fun b => (UScalar.ofNatCore (decodeByte b).val (decodeByte b).isLt : U8))=s.val := by
    induction s.val with
    | nil => rfl
    | cons b bs ih => simpa only [List.map_cons,decode_encode] using congrArg (List.cons b) ih
  congr 1
  apply Subtype.ext
  exact words

#print axioms decode_encode
#print axioms roundtrip
end AspisR1.F3U_Slice
end
