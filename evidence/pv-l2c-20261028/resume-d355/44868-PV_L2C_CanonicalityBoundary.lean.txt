import PV_L2C_M31
set_option autoImplicit false
namespace PV_L2C_CanonicalityBoundary
open PV_L2C_M31

/-- A representation diagnostic, not an input to the honest compiler. -/
def rawP : word := BitVec.ofNat 32 p

theorem same_image : decode rawP=decode 0 := by
  change (p : ZMod p)=0
  exact ZMod.natCast_self p
#print axioms same_image

theorem noncanonical : ¬ canonical rawP := by
  change ¬ p<p
  exact Nat.lt_irrefl p
#print axioms noncanonical

/-- Equality after the runjoin field projection alone cannot establish N3's
raw-word canonicality. No honest input or guard counterexample is asserted. -/
theorem decoded_equality_insufficient :
    ¬ (∀ x : word, decode x=decode 0 → canonical x) := by
  intro h
  exact noncanonical (h rawP same_image)
#print axioms decoded_equality_insufficient
end PV_L2C_CanonicalityBoundary
