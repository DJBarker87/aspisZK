import NDO_JFu_DigestSliceFacts
set_option autoImplicit false
namespace AspisR1.JFt_DigestInjective
open Aeneas Aeneas.Std Result

theorem fromLEBytes_cast {b : BitVec 32} {bs : List Byte}
    (same : bs=b.toLEBytes) : (BitVec.fromLEBytes bs).cast (by rw [same];simp [BitVec.toLEBytes_length])=b := by
  cases same
  rw [BitVec.fromLEBytes_toLEBytes (by decide : 32%8=0)]
  simp

theorem from_to (x : U32) : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x)=x := by
  have point : ∀ b : Byte,U8.bv (UScalar.mk b)=b := by intro b;rfl
  have map : List.map U8.bv (List.map UScalar.mk x.bv.toLEBytes)=x.bv.toLEBytes := by
    rw [List.map_map]
    simpa [Function.comp_def] using congrArg (fun f : Byte → Byte => List.map f x.bv.toLEBytes) (funext point)
  apply U32.bv_eq_imp_eq
  simp only [core.num.U32.from_le_bytes,core.num.U32.to_le_bytes]
  exact fromLEBytes_cast map

theorem word_length (x : U32) : (core.num.U32.to_le_bytes x).val.length=4 :=
  (core.num.U32.to_le_bytes x).property

@[simp] theorem take_word (x : U32) : (core.num.U32.to_le_bytes x).val.take 4=(core.num.U32.to_le_bytes x).val :=
  List.take_of_length_le (by rw [word_length])

theorem injective (a b : Array U32 8#usize)
    (same : AspisS6SourceCodec.DigestContents.chunks a=AspisS6SourceCodec.DigestContents.chunks b) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [a.property,b.property]
  · intro i ha hb
    have small : i<8 := by simpa only [a.property,show (8#usize).val=8 from rfl] using ha
    have selected:=congrArg (fun xs : List U8 => (xs.drop (4*i)).take 4) same
    have word : (core.num.U32.to_le_bytes a.val[i]).val=(core.num.U32.to_le_bytes b.val[i]).val := by
      interval_cases i <;>
        simpa [AspisS6SourceCodec.DigestContents.chunks,word_length,List.drop_append,List.take_append] using selected
    have arrays : core.num.U32.to_le_bytes a.val[i]=core.num.U32.to_le_bytes b.val[i] := Subtype.ext word
    simpa only [from_to] using congrArg core.num.U32.from_le_bytes arrays

#print axioms fromLEBytes_cast
#print axioms from_to
#print axioms word_length
#print axioms take_word
#print axioms injective
end AspisR1.JFt_DigestInjective
