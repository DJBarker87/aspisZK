import Mathlib.Algebra.Field.Basic

/-! Scalar zero-boundary facts. Source association is kept separate. -/
set_option autoImplicit false
namespace R1Z.PV_Inv_Guard
variable {K : Type} [Field K] [DecidableEq K]

def checkedInverse (x : K) : Option K := if x = 0 then none else some x⁻¹

theorem none_iff (x : K) : checkedInverse x = none ↔ x = 0 := by
  simp [checkedInverse]

theorem nonzero_branch (x : K) (h : x ≠ 0) : checkedInverse x = some x⁻¹ := by
  simp [checkedInverse,h]

theorem difference (chi slot : K) : checkedInverse (chi-slot) = none ↔ chi = slot := by
  rw [none_iff,sub_eq_zero]

theorem guarded (x : K) : (if x = 0 then none else checkedInverse x) = checkedInverse x := by
  by_cases h : x=0 <;> simp [checkedInverse,h]

#print axioms none_iff
#print axioms nonzero_branch
#print axioms difference
#print axioms guarded
end R1Z.PV_Inv_Guard
