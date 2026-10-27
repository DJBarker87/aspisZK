import RPz7_F3K_ArrayFacts
set_option autoImplicit false
namespace AspisR1.F3R_ArrayAccess
open Aeneas Aeneas.Std Result

theorem total {A : Type} {n : Usize} (v : Array A n) (i : Usize) (bound : i.val<n.val) :
    ∃ old put,Array.index_mut_usize v i=ok (old,put) := by
  have len : v.length=n.val := v.property
  obtain ⟨pair,called,rest⟩ := WP.spec_imp_exists (Array.index_mut_usize_spec v i (by omega))
  exact ⟨pair.1,pair.2,called⟩

#print axioms total
end AspisR1.F3R_ArrayAccess
