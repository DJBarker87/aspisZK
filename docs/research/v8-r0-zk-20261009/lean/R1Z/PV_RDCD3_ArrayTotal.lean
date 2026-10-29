import R1Z.PV_RDCD3_Total
namespace R1Z.PV_RDCD3_ArrayTotal
open Aeneas Aeneas.Std Result PV_RDCD3_Total
theorem update_total {T : Type} {N : Usize} (a : Array T N) (i : Usize) (x : T)
    (hi : i.val<N.val) : Total (Array.update a i x) := by
  obtain ⟨out,hout,_⟩ := WP.spec_imp_exists
    (Array.update_spec a i x (by change i.val<a.val.length; rw [a.property];exact hi))
  exact ⟨out,hout⟩


#print axioms update_total
end R1Z.PV_RDCD3_ArrayTotal
