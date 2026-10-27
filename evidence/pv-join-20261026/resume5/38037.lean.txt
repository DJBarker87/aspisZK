import R1Z.PV_Join_Canonical5
import R1Z.ProverRw18FieldMeaning
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_ArithmeticCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5
abbrev Raw := ProverRw18FieldMeaning.Raw
def old (x : aspis_core.field.QM31) : Raw :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
theorem full_old (x : aspis_core.field.QM31) : ProverRw18FieldMeaning.full (old x) = x := by
  cases x; rfl
theorem old_canonical (x : aspis_core.field.QM31) (hx : Q x) :
    ProverRw18FieldMeaning.Canonical (old x) := hx
theorem full_canonical (x : Raw) (hx : ProverRw18FieldMeaning.Canonical x) :
    Q (ProverRw18FieldMeaning.full x) := hx

theorem add (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, ProverRwDictionaryTower.qAdd x y = .ok z ∧ Q z := by
  obtain ⟨z,hz,hc,_⟩ := ProverRw18FieldMeaning.add (old x) (old y)
    (old_canonical x hx) (old_canonical y hy)
  rw [full_old,full_old] at hz
  exact ⟨_,hz,full_canonical z hc⟩
theorem mul (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y) :
    ∃ z, ProverRwDictionaryTower.qMul x y = .ok z ∧ Q z := by
  obtain ⟨z,hz,hc,_⟩ := ProverRw18FieldMeaning.mul (old x) (old y)
    (old_canonical x hx) (old_canonical y hy)
  rw [full_old,full_old] at hz
  exact ⟨_,hz,full_canonical z hc⟩

#print axioms full_old
#print axioms old_canonical
#print axioms full_canonical
#print axioms add
#print axioms mul
end R1Z.PV_Join_ArithmeticCanonical5
