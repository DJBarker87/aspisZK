import PV_B3P_Emission132
namespace PV_B3P_FreeTotal132
open Aeneas Aeneas.Std PV_B3P_132
set_option autoImplicit false

theorem if_ok (c : Prop) [Decidable c] (x y : Bool) :
    (if c then Result.ok x else Result.ok y) = Result.ok (if c then x else y) := by
  split <;> rfl
#print axioms if_ok

theorem total (row column : Usize) : ∃ b, reference132.free row column = .ok b := by
  obtain ⟨r,hr,hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=row) (y:=16#usize) (by decide))
  unfold reference132.free
  simp only [hr,lift,bind_tc_ok]
  simp only [if_ok]
  exact ⟨_,rfl⟩
#print axioms total
end PV_B3P_FreeTotal132
