import JFw_Chunks
set_option autoImplicit false
namespace AspisR1.JFw_BlockValidation
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical

theorem count (n : Nat) (b : List U8) : (JFw_Blocks.blocks n b).length = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [JFw_Blocks.blocks,List.length_cons,ih]

theorem success (n : Nat) (compact : List U8) (payload : Slice U8) (row : U8)
    (length : compact.length = 16*n) (bound : n ≤ Usize.max)
    (canon : canonical (bytesOf compact))
    (bytes : bytesOf payload.val = expand n (bytesOf compact)) :
    AspisR1RecordParser.r1_wire.validate_record_fields row payload = ok (.Ok ()) := by
  have same : payload.val = (JFw_Blocks.blocks n compact).flatten :=
    MultiproofConeByteEquality.bytes_injective (bytes.trans (JFw_Blocks.bytes n compact).symm)
  exact JFw_Chunks.validator payload (JFw_Blocks.blocks n compact) row same
    (by rw [count];exact bound) (JFw_Blocks.valid n compact length canon)

#print axioms count
#print axioms success
end AspisR1.JFw_BlockValidation
