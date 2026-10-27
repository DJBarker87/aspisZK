import R1Z.PV_Canon_Carrier
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std
 theorem d234_outside_domain : ¬ M (2147483648#u32) := by
  change ¬ (2147483648 < 2147483647)
  omega
 theorem modulus_outside_domain : ¬ M (2147483647#u32) := by
  change ¬ (2147483647 < 2147483647)
  omega
 theorem raw_constructor_has_no_invariant : ∃ x : U32, ¬ M x :=
  ⟨2147483648#u32,d234_outside_domain⟩
#print axioms d234_outside_domain
#print axioms modulus_outside_domain
#print axioms raw_constructor_has_no_invariant
end R1Z.PV_Canon
