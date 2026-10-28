import Aeneas
set_option autoImplicit false
namespace AspisR1.NCN_Cadence
open Aeneas Aeneas.Std

/-- The selected emitted push guard and frozen source mask have exactly the
same modulo-four cadence as the existing residue induction, on every Usize. -/
theorem word_mask (terms : Usize) : (terms &&& 3#usize).val = terms.val % 4 := by
  change terms.val &&& 3 = terms.val % 4
  simpa using Nat.and_two_pow_sub_one_eq_mod terms.val 2

theorem flush (terms : Usize) : (terms &&& 3#usize = 3#usize) ↔ terms.val % 4 = 3 := by
  have h := word_mask terms
  scalar_tac

#print axioms word_mask
#print axioms flush
end AspisR1.NCN_Cadence
