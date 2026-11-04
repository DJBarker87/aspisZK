import NGA_Accumulate
set_option autoImplicit false
namespace NGA_ArrayExt
open Aeneas Aeneas.Std Result NGA_Cell

theorem row_eq {α : Type} (s t : Array α 3#usize) (h : ∀ i : Fin 3, at3 s i=at3 t i) : s=t := by
 apply Subtype.ext
 apply List.ext_getElem
 · exact s.property.trans t.property.symm
 · intro i hi _
   have bound : i<3 := by simpa [s.property] using hi
   exact h ⟨i,bound⟩

theorem source (s t : Sums) (h : ∀ d : Cell, (get s d).val=(get t d).val) : s=t := by
 apply row_eq
 intro i
 apply row_eq
 intro j
 exact UScalar.eq_of_val_eq (h (i,j))

#print axioms row_eq
#print axioms source
end NGA_ArrayExt
