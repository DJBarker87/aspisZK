import F3J_OpeningFrame
import PSem_Validation
set_option autoImplicit false
namespace AspisR1.F3J_LengthFrame
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation SourceDigestAddresses
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft MultiproofConeCanonical

theorem cast_length (payload : Slice U8) (fits : payload.val.length<4294967296) :
    (UScalar.cast .U32 (Slice.len payload)).val=payload.val.length := by
  rw [UScalar.cast_val_eq]
  change payload.val.length%4294967296=payload.val.length
  exact Nat.mod_eq_of_lt fits

theorem framed (payload : Slice U8) (fits : payload.val.length<4294967296) :
    OraclePortCompactDraft.framed (bytesOf payload.val)=
      PublicInitFrame.lengthBytes (UScalar.cast .U32 (Slice.len payload)).val++rawBytes payload := by
  rw [cast_length payload fits]
  simp only [OraclePortCompactDraft.framed,bytesOf,List.length_map,PSem_Validation.length_encoding]
  rfl

#print axioms cast_length
#print axioms framed
end AspisR1.F3J_LengthFrame
