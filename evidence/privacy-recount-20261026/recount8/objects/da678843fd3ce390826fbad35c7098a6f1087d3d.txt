import R1Z.PV_RDB2C_PV_B2_D_ScalarOperations
set_option autoImplicit false
namespace PV_B2_D_QuarticCanonical
open Aeneas Aeneas.Std PV_B2_C_251FieldValue
open PV_B2_D_ScalarOperations
abbrev C := aspis_core.field.CM31
abbrev Q := aspis_core.field.QM31
def CC (x : C) : Prop := Canon x.a ∧ Canon x.b
def QC (x : Q) : Prop := CC x.c0 ∧ CC x.c1

theorem cadd (x y : C) (hx : CC x) (hy : CC y) : CC (aspis_core.field.CM31.add x y) :=
  ⟨add _ _ hx.1 hy.1,add _ _ hx.2 hy.2⟩
theorem csub (x y : C) (hx : CC x) (hy : CC y) : CC (aspis_core.field.CM31.sub x y) :=
  ⟨sub _ _ hx.1 hy.1,sub _ _ hx.2 hy.2⟩
-- Every multiplication result is canonical even when the source limbs are raw.
theorem cmul (x y : C) : CC (aspis_core.field.CM31.mul x y) := by
  dsimp only [CC,aspis_core.field.CM31.mul]
  constructor
  · apply sub <;> exact mul _ _
  · apply sub
    · apply sub
      · exact reduce _
      · exact mul _ _
    · exact mul _ _

theorem r_mul (x : C) (hx : CC x) : CC (aspis_core.field.mul_by_r x) :=
  ⟨sub _ _ (add _ _ hx.1 hx.1) hx.2,add _ _ hx.1 (add _ _ hx.2 hx.2)⟩

theorem qmul (x y : Q) : QC (aspis_core.field.QM31.mul x y) := by
  have h0 := cmul x.c0 y.c0
  have h1 := cmul x.c1 y.c1
  have h2 := cmul (aspis_core.field.CM31.add x.c0 x.c1)
    (aspis_core.field.CM31.add y.c0 y.c1)
  exact ⟨cadd _ _ h0 (r_mul _ h1),csub _ _ (csub _ _ h2 h0) h1⟩
#print axioms cadd
#print axioms csub
#print axioms cmul
#print axioms r_mul
#print axioms qmul
end PV_B2_D_QuarticCanonical
