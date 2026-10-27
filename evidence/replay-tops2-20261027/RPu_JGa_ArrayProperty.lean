import RPu_JFy_Steps
import RPu_FIy_ArraySlot
set_option autoImplicit false
namespace AspisR1.JGa_ArrayProperty
open Aeneas Aeneas.Std Result WP

@[step] theorem read {T : Type} {N : Usize} (a : Array T N) (i : Usize) (P : T → Prop)
    (hi : i.val<N.val) (ha : ∀ x∈a.val,P x) :
    Array.index_usize a i ⦃ out => P out ⦄ := by
  have spec : Array.index_usize a i ⦃ _ => True ⦄ := by step* <;> scalar_tac
  obtain ⟨x,hx,_⟩ := WP.spec_imp_exists spec
  rw [hx]
  exact ha x (List.mem_of_getElem? (FIy_ArraySlot.value a i x hx))
#print axioms read
end AspisR1.JGa_ArrayProperty
