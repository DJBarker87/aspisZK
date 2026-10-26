import FIp_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_PrefixFin
open Aeneas Aeneas.Std
open FIo_FieldBridge (NE)
open scoped BigOperators

theorem sum_range {N : Usize} (p k : Array NE N) (n : Nat) :
    FIp_Prefix.sumPrefix p k n=∑ j∈Finset.range n,FIp_ArrayValue.value k j*FIp_ArrayValue.value p j := by
  induction n with
  | zero => simp only [FIp_Prefix.zero,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [FIp_Prefix.succ,Finset.sum_range_succ,ih]

theorem sum_fin {N : Usize} (p k : Array NE N) (n : Nat) :
    FIp_Prefix.sumPrefix p k n=∑ j : Fin n,FIp_ArrayValue.value k j.val*FIp_ArrayValue.value p j.val := by
  rw [sum_range,←Fin.sum_univ_eq_sum_range]

#print axioms sum_range
#print axioms sum_fin
end AspisR1.FIp_PrefixFin
end
