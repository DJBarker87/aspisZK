import S6ByteInverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeLateWordRead

theorem u16_to_from (bytes : Array U8 2#usize) :
    core.num.U16.to_le_bytes (core.num.U16.from_le_bytes bytes)=bytes := by
  apply Subtype.ext
  change (((BitVec.fromLEBytes (bytes.val.map U8.bv)).cast (by simp only [List.length_map,bytes.property]; scalar_tac)).toLEBytes.map (fun b : Byte => (UScalar.mk b : U8)))=bytes.val
  rw [AspisS6ByteInverse.cast_toLE,AspisS6ByteInverse.toLE_fromLE,AspisS6ByteInverse.map_mk_bv]

@[step] theorem u16_read_spec (bytes : Array U8 2#usize) :
    lift (core.num.U16.from_le_bytes bytes) ⦃ result => result=core.num.U16.from_le_bytes bytes ⦄ := by
  apply exists_imp_spec
  exact ⟨_,rfl,rfl⟩

#print axioms u16_to_from
#print axioms u16_read_spec
end AspisS6NativeLateWordRead
