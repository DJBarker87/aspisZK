import R1Z.PV_OWNK_TowerCanon
set_option autoImplicit false
namespace R1Z.PV_OWNL_Scale
open Aeneas Aeneas.Std
open PV_OWNK_TowerCanon
/-- Source field.rs:338 and :975, late-lift scalar scaling, four reduced limbs. -/
def cmScale (x : C) (w : U32) : C :=
 ⟨PV_B2_FieldValue.aspis_core.field.M31.mul x.a w,
  PV_B2_FieldValue.aspis_core.field.M31.mul x.b w⟩
def scale (x : Q) (w : U32) : Q := ⟨cmScale x.c0 w,cmScale x.c1 w⟩
theorem canonical (x : Q) (w : U32) : Canon (scale x w) :=
 ⟨⟨PV_OWNK_ScalarOps.mul_canon _ _,PV_OWNK_ScalarOps.mul_canon _ _⟩,
  PV_OWNK_ScalarOps.mul_canon _ _,PV_OWNK_ScalarOps.mul_canon _ _⟩
#print axioms canonical
end R1Z.PV_OWNL_Scale
