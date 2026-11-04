import NFC_ArrayFour
set_option autoImplicit false
namespace AspisR1.NFG_ArrayWindow
open Aeneas Aeneas.Std
/-- A native arbitrary observed coordinate binds the complete fixed carrier. -/
theorem ext (xs ys : Array U64 4#usize)
 (observed : ∀ i : Fin 4, xs.val[i.val]! = ys.val[i.val]!) : xs=ys := by
 obtain ⟨a,b,c,d,hx⟩ := NFC_ArrayFour.shape xs
 obtain ⟨e,f,g,h,hy⟩ := NFC_ArrayFour.shape ys
 subst xs
 subst ys
 have h0:=observed ⟨0,by decide⟩
 have h1:=observed ⟨1,by decide⟩
 have h2:=observed ⟨2,by decide⟩
 have h3:=observed ⟨3,by decide⟩
 simp only [Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ] at h0 h1 h2 h3
 cases h0
 cases h1
 cases h2
 cases h3
 rfl
#print axioms ext
end AspisR1.NFG_ArrayWindow
