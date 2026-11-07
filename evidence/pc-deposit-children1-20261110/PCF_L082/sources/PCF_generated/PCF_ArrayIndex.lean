import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_ArrayIndex
theorem result {T : Type} [Inhabited T] {n : Usize} (a : Array T n) (i : Usize)
    (bounds : i.val < a.length) : a.index_usize i = ok (a.val[i.val]!) := by
  obtain ⟨out,ho,vo⟩ := WP.spec_imp_exists (Array.index_usize_spec a i bounds)
  subst out
  simpa only [List.getElem!_pos] using ho
#print axioms result
end PCF_ArrayIndex
