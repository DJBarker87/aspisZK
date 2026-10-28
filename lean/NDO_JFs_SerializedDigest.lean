import JFs_SerializerLengths
import RPz7_S6NativeDigestAcceptedInverseV1
set_option autoImplicit false
namespace AspisR1.JFs_SerializedDigest
open Aeneas Aeneas.Std Result WP
open AspisR1PublicSerializer.FieldsRefinement431

theorem shape (a : Array U32 8#usize) : encodeWords a.val=AspisS6SourceCodec.DigestContents.chunks a := by
  have expansion : a.val=[a.val[0]'(by rw [a.property];decide),a.val[1]'(by rw [a.property];decide),
      a.val[2]'(by rw [a.property];decide),a.val[3]'(by rw [a.property];decide),
      a.val[4]'(by rw [a.property];decide),a.val[5]'(by rw [a.property];decide),
      a.val[6]'(by rw [a.property];decide),a.val[7]'(by rw [a.property];decide)] := by
    apply List.ext_getElem
    · simp only [a.property,List.length_cons,List.length_nil]
      rfl
    · intro i hi hj
      have small : i<8 := by simpa only [a.property,show (8#usize).val=8 from rfl] using hi
      interval_cases i <;> rfl
  conv_lhs => rw [expansion]
  simp only [encodeWords,List.flatMap_cons,List.flatMap_nil,wordBytes,List.append_nil,
    AspisS6SourceCodec.DigestContents.chunks,List.append_assoc]

theorem decoded (bytes : Array U8 32#usize) (a : Array U32 8#usize)
    (call : AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes=ok (.Ok a)) :
    encodeWords a.val=bytes.val := by
  have contents:=AspisS6NativeDigestAcceptedInverse.decoded_contents bytes
  rw [call,WP.spec_ok] at contents
  exact (shape a).trans (contents a rfl)

#print axioms shape
#print axioms decoded
end AspisR1.JFs_SerializedDigest
