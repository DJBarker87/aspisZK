import Aeneas.Std
namespace PV_B3P_HelperIndex224
open Aeneas Aeneas.Std
set_option autoImplicit false

def zero {α : Type} (xs : Array α 2#usize) : α :=
  xs.val[0]'(by have h := xs.property; scalar_tac)
def one {α : Type} (xs : Array α 2#usize) : α :=
  xs.val[1]'(by have h := xs.property; scalar_tac)

theorem index_zero {α : Type} (xs : Array α 2#usize) :
    Array.index_usize xs 0#usize = .ok (zero xs) := by
  obtain ⟨v,hv,hval⟩ := WP.spec_imp_exists (Array.index_usize_spec xs 0#usize (by
    have h := xs.property; scalar_tac))
  simpa only [zero,hval,show (0#usize).val = 0 from rfl] using hv

theorem index_one {α : Type} (xs : Array α 2#usize) :
    Array.index_usize xs 1#usize = .ok (one xs) := by
  obtain ⟨v,hv,hval⟩ := WP.spec_imp_exists (Array.index_usize_spec xs 1#usize (by
    have h := xs.property; scalar_tac))
  simpa only [one,hval,show (1#usize).val = 1 from rfl] using hv

#print axioms index_zero
#print axioms index_one
end PV_B3P_HelperIndex224
