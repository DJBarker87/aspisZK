import LPi_WriterValues
set_option autoImplicit false
namespace AspisR1.LPi_SerializationFold
open Aeneas Aeneas.Std Result OraclePortCkptAbi2Extracted
abbrev Q := aspis_core.field.QM31

def append (buf : List U8) (x : Q) : List U8 := buf ++ CheckpointP6EncodeK.bytes x

def fold (buf : List U8) : List Q → List U8
  | [] => buf
  | x::xs => fold (append buf x) xs

/-- The native one-iteration put_k cut consumes exactly this append law.
This induction quantifies every initial buf and every sequence of fields. -/
theorem contents (buf : List U8) (xs : List Q) :
    fold buf xs = buf ++ xs.flatMap CheckpointP6EncodeK.bytes := by
  induction xs generalizing buf with
  | nil => simp only [fold,List.flatMap_nil,List.append_nil]
  | cons x xs ih =>
    simpa only [fold,append,ih,List.flatMap_cons,List.append_assoc]

theorem byte_length (x : Q) : (CheckpointP6EncodeK.bytes x).length = 16 := by
  simp [CheckpointP6EncodeK.bytes,core.num.U32.to_le_bytes,BitVec.toLEBytes]

theorem length (buf : List U8) (xs : List Q) :
    (fold buf xs).length = buf.length + 16*xs.length := by
  induction xs generalizing buf with
  | nil => simp [fold]
  | cons x xs ih =>
    simp only [fold,ih,append,List.length_append,byte_length,List.length_cons]
    omega

/-- Exactly64 fields, arbitrary valid raw coordinates and arbitrary buf.
The 712-byte buf invariant implies the checksum input is1736 bytes. -/
theorem weights64 (buf : List U8) (xs : List Q)
    (hp : buf.length = 712) (hx : xs.length = 64) :
    fold buf xs = buf ++ xs.flatMap CheckpointP6EncodeK.bytes ∧
      (fold buf xs).length = 1736 := by
  exact ⟨contents buf xs,by rw [length,hp,hx]⟩

#print axioms contents
#print axioms byte_length
#print axioms length
#print axioms weights64
end AspisR1.LPi_SerializationFold
