import PV_B3P_Emission132
namespace PV_B3P_FreeTotal132
open Aeneas Aeneas.Std PV_B3P_132
set_option autoImplicit false

theorem total (row column : Usize) : ∃ b, reference132.free row column = .ok b := by
  obtain ⟨r,hr,hrval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=row) (y:=16#usize) (by decide))
  unfold reference132.free
  simp only [hr,lift,bind_tc_ok]
  repeat first
    | exact ⟨_,rfl⟩
    | (split <;> try simp only [lift,bind_tc_ok])
#print axioms total
end PV_B3P_FreeTotal132
