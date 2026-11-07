import NMT_345Carriers
set_option autoImplicit false
namespace NMT_345
open Aeneas Aeneas.Std
#print Aeneas.Std.instBEqUScalar_1
/-- The native machine-word length comparison equals the canonical Nat
comparison; no concrete account or buffer is enumerated. -/
theorem scalar_size_compare (n : Usize) :
 (n.val != RSL.CHECKPOINT_BYTES) = (n != 1768#usize) := by
 simp [bne,Aeneas.Std.instBEqUScalar_1,RSL.CHECKPOINT_BYTES]
 constructor
 · intro h; exact UScalar.eq_of_val_eq h
 · intro h; subst n; rfl
#print axioms scalar_size_compare
end NMT_345
