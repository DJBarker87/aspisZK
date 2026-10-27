import LPi_WriterValues
set_option autoImplicit false
namespace AspisR1.LPi_SerializationFold
open Aeneas Aeneas.Std Result OraclePortCkptAbi2Extracted
abbrev Q := aspis_core.field.QM31

def append (prefix : List U8) (x : Q) : List U8 := prefix ++ CheckpointP6EncodeK.bytes x

def fold (prefix : List U8) : List Q → List U8
  | [] => prefix
  | x::xs => fold (append prefix x) xs

/-- The native one-iteration put_k cut consumes exactly this append law.
This induction quantifies every initial prefix and every sequence of fields. -/
theorem contents (prefix : List U8) (xs : List Q) :
    fold prefix xs = prefix ++ xs.flatMap CheckpointP6EncodeK.bytes := by
  induction xs generalizing prefix with
  | nil => simp only [fold,List.flatMap_nil,List.append_nil]
  | cons x xs ih =>
    simpa only [fold,append,ih,List.flatMap_cons,List.append_assoc]

theorem byte_length (x : Q) : (CheckpointP6EncodeK.bytes x).length = 16 := by
  simp [CheckpointP6EncodeK.bytes,core.num.U32.to_le_bytes,BitVec.toLEBytes]

theorem length (prefix : List U8) (xs : List Q) :
    (fold prefix xs).length = prefix.length + 16*xs.length := by
  induction xs generalizing prefix with
  | nil => simp [fold]
  | cons x xs ih =>
    simp only [fold,ih,append,List.length_append,byte_length,List.length_cons]
    omega

/-- Exactly64 fields, arbitrary valid raw coordinates and arbitrary prefix.
The 712-byte prefix invariant implies the checksum input is1736 bytes. -/
theorem weights64 (prefix : List U8) (xs : List Q)
    (hp : prefix.length = 712) (hx : xs.length = 64) :
    fold prefix xs = prefix ++ xs.flatMap CheckpointP6EncodeK.bytes ∧
      (fold prefix xs).length = 1736 := by
  exact ⟨contents prefix xs,by rw [length,hp,hx]⟩

#print axioms contents
#print axioms byte_length
#print axioms length
#print axioms weights64
end AspisR1.LPi_SerializationFold
