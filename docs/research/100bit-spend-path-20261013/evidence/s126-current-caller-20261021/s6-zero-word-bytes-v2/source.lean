import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisS6ZeroWord

/-- Symbolic zero-word serialization: no field-value enumeration or large
kernel reduction of byte arrays. -/
theorem zero_bytes (n : Nat) :
    (0#(8*n)).toLEBytes=List.replicate n (0#8) := by
  apply List.ext_getElem
  · simp [BitVec.toLEBytes_length]
    omega
  · intro i hi hj
    simp only [List.getElem_replicate]
    apply (Byte.eq_iff _ _).2
    intro j hj8
    have hi' : i<n := by simpa using hj
    have hbit : 8*i+j<8*n := by omega
    rw [BitVec.toLEBytes_getElem_testBit _ i j hi ⟨hj8,hbit⟩]
    simp [Byte.testBit]

theorem u32_zero :
    (core.num.U32.to_le_bytes (0#u32)).val=List.replicate 4 0#u8 := by
  change (0#(8*4)).toLEBytes.map (fun b : Byte => (UScalar.mk b : U8))=
    List.replicate 4 0#u8
  rw [zero_bytes]
  simp
  scalar_tac

#print axioms zero_bytes
#print axioms u32_zero
end AspisS6ZeroWord
