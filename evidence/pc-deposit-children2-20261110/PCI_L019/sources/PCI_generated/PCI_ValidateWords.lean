import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_ValidateWords
/-- Explicit same-word carrier map; not a truncating cast. -/
def word (x : UInt32) : U32 := U32.ofNat x.toNat (by
  have h := UInt32.toNat_lt x
  change x.toNat ≤ 4294967295
  omega)

theorem word_value (x : UInt32) : (word x).val=x.toNat := rfl

theorem word_eq (x y : UInt32) : word x=word y ↔ x=y := by
  constructor
  · intro h
    have hv := congrArg UScalar.val h
    exact UInt32.toNat_inj.mp hv
  · intro h
    subst y
    rfl

#print axioms word_value
#print axioms word_eq
end PCI_ValidateWords
