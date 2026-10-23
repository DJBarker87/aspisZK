import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisS6ByteInverse

/-- Symbolic byte identity; no finite enumeration or large word reduction. -/
theorem toLE_fromLE (bytes : List Byte) :
    (BitVec.fromLEBytes bytes).toLEBytes=bytes := by
  apply List.ext_getElem
  · rw [BitVec.toLEBytes_length]
    omega
  · intro i hi hinput
    apply (Byte.eq_iff _ _).2
    intro j hj
    have hbit : 8*i+j<8*bytes.length := by omega
    rw [BitVec.toLEBytes_getElem_testBit _ i j hi ⟨hj,hbit⟩,
      BitVec.fromLEBytes_getElem bytes (8*i+j) hbit]
    have hdiv : (8*i+j)/8=i := by omega
    have hmod : (8*i+j)%8=j := by omega
    simp only [hdiv,hmod]

theorem cast_toLE {n m : Nat} (value : BitVec n) (h : n=m) :
    (value.cast h).toLEBytes=value.toLEBytes := by
  cases h
  rfl

theorem map_mk_bv (bytes : List U8) :
    (bytes.map U8.bv).map (fun b : Byte => (UScalar.mk b : U8))=bytes := by
  rw [List.map_map]
  have he : (fun b : U8 => (UScalar.mk (U8.bv b) : U8))=id := by
    funext b
    cases b
    rfl
  change List.map (fun b : U8 => (UScalar.mk (U8.bv b) : U8)) bytes=bytes
  rw [he,List.map_id]

/-- Complete original four bytes are recovered, without canonicality premises. -/
theorem u32_to_from (bytes : Array U8 4#usize) :
    core.num.U32.to_le_bytes (core.num.U32.from_le_bytes bytes)=bytes := by
  apply Subtype.ext
  change (((BitVec.fromLEBytes (bytes.val.map U8.bv)).cast _).toLEBytes.map UScalar.mk)=bytes.val
  rw [cast_toLE,toLE_fromLE,map_mk_bv]

theorem u64_to_from (bytes : Array U8 8#usize) :
    core.num.U64.to_le_bytes (core.num.U64.from_le_bytes bytes)=bytes := by
  apply Subtype.ext
  change (((BitVec.fromLEBytes (bytes.val.map U8.bv)).cast _).toLEBytes.map UScalar.mk)=bytes.val
  rw [cast_toLE,toLE_fromLE,map_mk_bv]

#print axioms toLE_fromLE
#print axioms u32_to_from
#print axioms u64_to_from
end AspisS6ByteInverse
