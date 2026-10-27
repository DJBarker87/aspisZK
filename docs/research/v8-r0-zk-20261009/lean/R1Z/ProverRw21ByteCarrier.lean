import R1Z.ProverRw21ModelBytes
import R1Z.ProverCommitWordBytes47
set_option autoImplicit false
namespace R1Z.ProverRw21ByteCarrier
open Aeneas Aeneas.Std

def decode (b : U8) : UInt8 := ⟨b.bv⟩

theorem decode_encode (b : UInt8) : decode (ProverRw19MathematicalAssembly.byte b)=b := by cases b; rfl
theorem encode_decode (b : U8) : ProverRw19MathematicalAssembly.byte (decode b)=b := by cases b; rfl

def equivalence : U8 ≃ UInt8 where
  toFun := decode
  invFun := ProverRw19MathematicalAssembly.byte
  left_inv := encode_decode
  right_inv := decode_encode

theorem decode_raw (b : U8) : (decode b).toFin=ProverCommitWordBytes47.rawByte b := rfl

theorem decode_encode_list (xs : List UInt8) :
    (xs.map ProverRw19MathematicalAssembly.byte).map decode=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,decode_encode,ih]

theorem encode_decode_list (xs : List U8) :
    (xs.map decode).map ProverRw19MathematicalAssembly.byte=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,encode_decode,ih]

theorem decode_list_injective (xs ys : List U8) (h : xs.map decode=ys.map decode) : xs=ys := by
  rw [← encode_decode_list xs,← encode_decode_list ys,h]

theorem word_bytes (x : U32) :
    ((core.num.U32.to_le_bytes x).val.map decode).map UInt8.toFin=
      List.ofFn (AspisR1.RetainedFieldByteCodec.encodeWordLE (ProverCommitWordBytes47.rawWord x)) := by
  rw [List.map_map]
  exact ProverCommitWordBytes47.word x

#print axioms decode
#print axioms decode_encode
#print axioms encode_decode
#print axioms equivalence
#print axioms decode_raw
#print axioms decode_encode_list
#print axioms encode_decode_list
#print axioms decode_list_injective
#print axioms word_bytes
end R1Z.ProverRw21ByteCarrier
