import PV_B3_CanonicalCarrier
set_option autoImplicit false
namespace PV_B3_Canonical
open Aeneas Aeneas.Std Result
 theorem index_total {α : Type} {n : Usize} (xs : Array α n) (i : Usize) (hi : i.val < n.val) :
    ∃ x, Array.index_usize xs i = .ok x := by
  have bound : i.val < xs.val.length := by rw [xs.property]; exact hi
  obtain ⟨x,hx,_⟩ := WP.spec_imp_exists (Array.index_usize_spec xs i bound)
  exact ⟨x,hx⟩
#print axioms index_total
end PV_B3_Canonical
