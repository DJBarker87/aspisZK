import PV_B3_FieldTransport
namespace PV_B3_PreparedCarrier
open Aeneas Aeneas.Std Result PV_B3_FieldTransport
set_option autoImplicit false
abbrev NewP := PV_B3_Copy_117.host_arithmetic.PreparedQm31Multiplier
abbrev OldP := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier
def toP (x : NewP) : OldP := ⟨x.components⟩
def fromP (x : OldP) : NewP := ⟨x.components⟩
theorem left (x : NewP) : fromP (toP x) = x := by cases x; rfl
theorem right (x : OldP) : toP (fromP x) = x := by cases x; rfl
#print axioms toP
#print axioms fromP
#print axioms left
#print axioms right
end PV_B3_PreparedCarrier
