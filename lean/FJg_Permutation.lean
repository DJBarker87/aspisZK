import FJc_PermTable
set_option autoImplicit false
namespace AspisR1.FJg_Permutation

theorem value (s : Fin 4) : FJc_LowModel.perm s.val=(4-s.val)%4 := by
  rw [FJc_PermTable.formula s.val s.isLt]
  by_cases h : s.val=0
  · simp only [h,ite_true,Nat.sub_zero,Nat.mod_self]
  · rw [if_neg h,Nat.mod_eq_of_lt]
    have := s.isLt
    omega
#print axioms value
end AspisR1.FJg_Permutation
