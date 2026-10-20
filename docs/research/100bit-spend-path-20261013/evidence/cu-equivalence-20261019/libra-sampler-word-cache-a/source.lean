import AspisV8R19.SamplerWordRead
import AspisV8R19.SqueezeOracleBridge
import AspisV8R19.SamplerWords

/-! Runtime little-endian decoding equals the retained integer byte model.
Symbolic byte concatenation avoids concrete normalization of large words. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerWordBridge
open Aeneas Aeneas.Std AspisR72Sampler SamplerWordRead SqueezeOracleBridge
open SourceDuplexStep

theorem byte_cons (b : BitVec 8) (l : List (BitVec 8)) :
    (BitVec.fromLEBytes (b::l)).toNat = (BitVec.fromLEBytes l).toNat*256+b.toNat := by
  have he : BitVec.fromLEBytes (b::l) =
      ((BitVec.fromLEBytes l) ++ b).setWidth (8*(b::l).length) := by
    rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or]
    change _ ||| _ = _ ||| _
    exact BitVec.or_comm _ _
  rw [he,BitVec.toNat_setWidth]
  have hb : ((BitVec.fromLEBytes l) ++ b).toNat < 2^(8*(b::l).length) := by
    have h := ((BitVec.fromLEBytes l) ++ b).isLt
    simpa only [List.length_cons,Nat.mul_add,Nat.mul_one] using h
  rw [Nat.mod_eq_of_lt hb,BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

theorem four_bytes (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val =
      a.val+256*b.val+65536*c.val+16777216*d.val := by
  change (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv]).toNat = _
  simp only [byte_cons]
  change (((0*256+d.val)*256+c.val)*256+b.val)*256+a.val = _
  omega

theorem four_contents (s : State) (j : Fin 8) :
    (four (encodeState s) (4*j.val) (by omega)).val =
      [encodeByte (s ⟨4*j.val,by omega⟩),
       encodeByte (s ⟨4*j.val+1,by omega⟩),
       encodeByte (s ⟨4*j.val+2,by omega⟩),
       encodeByte (s ⟨4*j.val+3,by omega⟩)] := by
  apply List.ext_getElem
  · have h := (four (encodeState s) (4*j.val) (by omega)).property
    exact h
  · intro i hi hj
    have hi4 : i < 4 := by simpa using hj
    simp only [four,List.getElem_take,List.getElem_drop,encodeState,bytes,
      List.getElem_map,List.getElem_ofFn]
    interval_cases i <;> rfl

theorem source_word (s : State) (j : Fin 8) :
    (core.num.U32.from_le_bytes (four (encodeState s) (4*j.val) (by omega))).val =
      SamplerWords.word s j := by
  have ha : four (encodeState s) (4*j.val) (by omega) =
      Array.make 4#usize [encodeByte (s ⟨4*j.val,by omega⟩),
        encodeByte (s ⟨4*j.val+1,by omega⟩),encodeByte (s ⟨4*j.val+2,by omega⟩),
        encodeByte (s ⟨4*j.val+3,by omega⟩)] := by
    apply Subtype.ext
    exact four_contents s j
  rw [ha,four_bytes]
  rfl

theorem source_mask (word : U32) :
    (word &&& field.P).val = SamplerWords.masked 31 word.val := by
  change (word.bv &&& field.P.bv).toNat = _
  rw [BitVec.toNat_and]
  simp only [SamplerWords.source31_mask,field.P]
  rfl

#print axioms byte_cons
#print axioms four_bytes
#print axioms four_contents
#print axioms source_word
#print axioms source_mask
end AspisV8R19.SamplerWordBridge
