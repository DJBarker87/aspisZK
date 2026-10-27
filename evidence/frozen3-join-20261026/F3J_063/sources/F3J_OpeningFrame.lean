import F3J_OpeningFacts
set_option autoImplicit false
namespace AspisR1.F3J_OpeningFrame
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation SourceDigestAddresses
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem absorb (s : Array U8 32#usize) (tag : U8) (n : U32) (payload : Slice U8) :
    flatten (CallerStep.openingAbsorbParts s tag n payload)=
      bytes (decodeState s)++[0,decodeByte tag]++PublicInitFrame.lengthBytes n.val++rawBytes payload := by
  simp only [CallerStep.openingAbsorbParts,flatten,Array.to_slice,Array.make,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]
  simp only [← state_bytes,length_bytes,rawBytes,List.map_append,decode_zero,List.map_cons,List.map_nil,List.append_assoc]
  rfl

#print axioms absorb
end AspisR1.F3J_OpeningFrame
