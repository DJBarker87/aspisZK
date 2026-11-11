import PIN2_ProbeSemanticPublicHelpers
/-! PIN2 W11 (2026-11-11), NKR batch, PIN2P route.  A SCOPED coercion from the PIN2 semantic
public (`PIN2P.SemanticPublic`, W3c probe-crate struct) to the pre-PIN2 native struct, by
`PIN2P.SemanticPublic.dropDestination`.  A module that opens this scope and binds `p` at the PIN2
type gets every pre-PIN2 native read elaborated as exactly `PIN2P.SemanticPublic.dropDestination p`
(the same term W3c's OnRun modules write by hand).  No coercion in the other direction exists, so a
native public can never be silently promoted to a PIN2 one (no `embed`). -/
set_option autoImplicit false
namespace AspisR1.PIN2W11_DropCoe
scoped instance : Coe PIN2P.SemanticPublic PIN2P.OldSP := ⟨PIN2P.SemanticPublic.dropDestination⟩
theorem coe_eq (p : PIN2P.SemanticPublic) :
    (p : PIN2P.OldSP) = PIN2P.SemanticPublic.dropDestination p := rfl
#print axioms coe_eq
end AspisR1.PIN2W11_DropCoe
