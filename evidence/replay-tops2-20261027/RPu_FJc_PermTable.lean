import RPu_FJc_LowModel
set_option autoImplicit false
namespace AspisR1.FJc_PermTable
open Aeneas Aeneas.Std

theorem formula (i : Nat) (hi : i<4) : FJc_LowModel.perm i=if i=0 then 0 else 4-i := by
  interval_cases i <;> norm_num [FJc_LowModel.perm,FIo_Native.weights.PERM,Array.make]

theorem bound (i : Nat) (hi : i<4) : FJc_LowModel.perm i<4 := by
  rw [formula i hi]
  split <;> omega
#print axioms formula
#print axioms bound
end AspisR1.FJc_PermTable
