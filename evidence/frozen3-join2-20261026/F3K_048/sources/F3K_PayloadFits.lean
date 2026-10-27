import F3J_LengthFrame
set_option autoImplicit false
namespace AspisR1.F3K_PayloadFits
open Aeneas Aeneas.Std
open OraclePortCompactDraft MultiproofConeCanonical

theorem fits (payload : Slice U8) (rowBytes : AspisV8R19.DuplexFrames.Bytes)
    (frame : rowBytes=framed (bytesOf payload.val))
    (bound : rowBytes.length≤SelectedTranscriptParams.D) :
    payload.val.length<4294967296 := by
  rw [frame] at bound
  have length : (framed (bytesOf payload.val)).length=4+payload.val.length := by
    simp only [framed,List.length_append,bytesOf,List.length_map]
    rfl
  rw [length] at bound
  have cap : SelectedTranscriptParams.D<4294967296 := by decide
  omega

#print axioms fits
end AspisR1.F3K_PayloadFits
