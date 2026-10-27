import JFu_DigestSliceFacts
set_option autoImplicit false
namespace AspisR1.JFt_DigestInjective
open Aeneas Aeneas.Std Result

theorem from_to (x : U32) : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x)=x := by
  apply U32.bv_eq_imp_eq
  have map : List.map U8.bv (List.map UScalar.mk x.bv.toLEBytes)=x.bv.toLEBytes := by
    simp only [List.map_map,Function.comp_def,show (fun b : Byte => U8.bv (UScalar.mk b))=id from rfl,List.map_id]
  simp only [core.num.U32.from_le_bytes,core.num.U32.to_le_bytes]
  rw [map,BitVec.fromLEBytes_toLEBytes (by decide : 32%8=0)]
  simp

theorem word_length (x : U32) : (core.num.U32.to_le_bytes x).val.length=4 :=
  (core.num.U32.to_le_bytes x).property

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
        simpa only [AspisS6SourceCodec.DigestContents.chunks,word_length,List.length_append,
          Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub,List.drop_append,List.take_append,
          List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,
          List.nil_append,List.append_nil] using selected
    have arrays : core.num.U32.to_le_bytes a.val[i]=core.num.U32.to_le_bytes b.val[i] := Subtype.ext word
    simpa only [from_to] using congrArg core.num.U32.from_le_bytes arrays

#print axioms from_to
#print axioms word_length
#print axioms injective
end AspisR1.JFt_DigestInjective
