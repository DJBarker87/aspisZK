import Mathlib.Tactic
set_option autoImplicit false
namespace PV_L2D_Read4

abbrev Bytes := Fin 32 → UInt8

def offset (word : Fin 8) (byte : Fin 4) : Fin 32 :=
  ⟨4*word.val+byte.val,by have:=word.isLt;have:=byte.isLt;omega⟩

def slice (block : Bytes) (word : Fin 8) : List UInt8 :=
  ((List.ofFn block).drop (4*word.val)).take 4

def array (block : Bytes) (word : Fin 8) : List UInt8 :=
  List.ofFn (fun j : Fin 4 => block (offset word j))

theorem slice_length (block : Bytes) (word : Fin 8) : (slice block word).length=4 := by
  simp only [slice,List.length_take,List.length_drop,List.length_ofFn]
  have:=word.isLt
  omega
#print axioms slice_length

theorem conversion_bytes (block : Bytes) (word : Fin 8) : slice block word=array block word := by
  apply List.ext_getElem
  · simp only [slice_length,array,List.length_ofFn]
  · intro i hi hi'
    simp only [slice,List.getElem_take,List.getElem_drop,List.getElem_ofFn,
      array,offset] at *
#print axioms conversion_bytes

/-- Both source forms pass exactly the same four bytes to from_le_bytes;
the decoder itself is not replaced or approximated. -/
theorem decode_same {A : Type} (decode : List UInt8 → A) (block : Bytes) (word : Fin 8) :
    decode (slice block word)=decode (array block word) := by
  rw [conversion_bytes]
#print axioms decode_same

theorem last_word_offsets :
    (offset ⟨7,by decide⟩ ⟨0,by decide⟩).val=28 ∧
    (offset ⟨7,by decide⟩ ⟨3,by decide⟩).val=31 := by decide
#print axioms last_word_offsets
end PV_L2D_Read4
