import F3K_QueryWords
import AeneasWordCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_WordCodec
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
open RetainedFieldByteCodec AeneasWordCodec

def bytes4 (a : Array U8 4#usize) : WordBytes := fun i=>decodeByte (a.val[i.val]'(by have h : a.val.length=4:=a.property;omega))

theorem carrier (a : Array U8 4#usize) :
    aeneasWord (bytes4 a)=core.num.U32.from_le_bytes a := by
  unfold aeneasWord
  apply congrArg core.num.U32.from_le_bytes
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.symm
  · intro i hi hj
    have hi4 : i<4 := by simpa using hi
    interval_cases i <;> simp only [Array.make,bytes4,word_roundtrip,List.getElem_cons_zero,List.getElem_cons_succ] <;> rfl

theorem encoded_list (w : U32) :
    (core.num.U32.to_le_bytes w).val.map (fun x=>x.bv)=w.bv.toLEBytes := by
  simp only [core.num.U32.to_le_bytes,List.map_map,Function.comp_def,List.map_id_fun]
  change List.map id w.bv.toLEBytes=w.bv.toLEBytes
  exact List.map_id _

theorem roundtrip (w : U32) :
    core.num.U32.from_le_bytes (core.num.U32.to_le_bytes w)=w := by
  apply UScalar.eq_of_val_eq
  change (BitVec.fromLEBytes ((core.num.U32.to_le_bytes w).val.map (fun x=>x.bv))).toNat=w.val
  rw [encoded_list,BitVec.fromLEBytes_toLEBytes (by decide)]
  rfl

theorem encoding (w : U32) :
    bytes4 (core.num.U32.to_le_bytes w)=encodeWordLE ⟨w.val,w.bv.isLt⟩ := by
  have decoded := aeneasWord_val_eq (bytes4 (core.num.U32.to_le_bytes w))
  rw [carrier,roundtrip] at decoded
  have word : decodeWordLE (bytes4 (core.num.U32.to_le_bytes w))=⟨w.val,w.bv.isLt⟩ := Fin.ext decoded.symm
  have inverse := encodeWordLE_decodeWordLE (bytes4 (core.num.U32.to_le_bytes w))
  rw [word] at inverse
  exact inverse.symm

#print axioms carrier
#print axioms encoded_list
#print axioms roundtrip
#print axioms encoding
end AspisR1.F3K_WordCodec
end
