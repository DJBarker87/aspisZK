import NGK_COMBINED_IMPORT
set_option autoImplicit false
namespace AspisR1.NGQ_ByteFrames
open Aeneas Aeneas.Std Result
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize

def byte (a : Bytes32) (j : Fin 32) : U8 :=
 a.val[j.val]'(by have := a.property; change a.val.length=32 at this; omega)
def block (a : Blocks) (p : Fin 8) : Bytes32 :=
 a.val[p.val]'(by have := a.property; change a.val.length=8 at this; omega)

theorem bytes_ext (a b : Bytes32) (windows : ∀ j, (byte a j).val=(byte b j).val) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · intro j hj hk
    have bound : j<32 := by have h:=a.property; change a.val.length=32 at h; omega
    exact UScalar.eq_of_val_eq (windows ⟨j,bound⟩)

theorem blocks_ext (a b : Blocks) (windows : ∀ p j, (byte (block a p) j).val=(byte (block b p) j).val) : a=b := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact a.property.trans b.property.symm
  · intro p hp hq
    have bound : p<8 := by have h:=a.property; change a.val.length=8 at h; omega
    exact bytes_ext _ _ (windows ⟨p,bound⟩)

theorem set_block (a : Blocks) (i : Usize) (x : Bytes32) (hi : i.val<8) (p : Fin 8) :
    block (a.set i x) p=if p.val=i.val then x else block a p := by
  by_cases equal : p.val=i.val
  · subst_vars
    simp only [block,Array.set,if_pos rfl,List.getElem_set_self]
  · simp only [block,Array.set,if_neg equal,List.getElem_set_ne equal]

/-- The arbitrary native byte window determines the entire same buffer,
including every untouched block. This is the required frame composition. -/
theorem write_from_windows (before after : Blocks) (i : Usize) (reply : Bytes32)
    (hi : i.val<8)
    (windows : ∀ p j, (byte (block after p) j).val=
      (byte (if p.val=i.val then reply else block before p) j).val) :
    after=before.set i reply := by
  apply blocks_ext
  intro p j
  rw [set_block before i reply hi p]
  exact windows p j

#print axioms bytes_ext
#print axioms blocks_ext
#print axioms set_block
#print axioms write_from_windows
end AspisR1.NGQ_ByteFrames
