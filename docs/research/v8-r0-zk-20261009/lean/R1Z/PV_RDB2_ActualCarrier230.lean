import R1Z.PV_RDB2_FullTypes
import R1Z.PV_RDB2_230_Types
set_option autoImplicit false
namespace PV_B1_ActualCarrier230
abbrev HQ := ProverRwFull.aspis_core.field.QM31
abbrev Q := PV_B1_230.aspis_core.field.QM31

def toQ (x : HQ) : Q :=
  { c0 := { a := x.c0.a, b := x.c0.b }, c1 := { a := x.c1.a, b := x.c1.b } }

def fromQ (x : Q) : HQ :=
  { c0 := { a := x.c0.a, b := x.c0.b }, c1 := { a := x.c1.a, b := x.c1.b } }

theorem from_to (x : HQ) : fromQ (toQ x)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rfl

theorem to_from (x : Q) : toQ (fromQ x)=x := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  rfl

theorem injective (a b : HQ) : toQ a=toQ b ↔ a=b := by
  constructor
  · intro h
    have hr := congrArg fromQ h
    simpa only [from_to] using hr
  · intro h
    cases h
    rfl
#print axioms from_to
#print axioms to_from
#print axioms injective
end PV_B1_ActualCarrier230
