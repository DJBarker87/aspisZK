import R1Z.PV_RunJoin_WeightCounters46
import R1Z.PV_RunJoin_WeightPointRows46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightRowCounters47
open Aeneas Aeneas.Std Result

theorem sub_small (a b : Usize) (h : b.val≤a.val) :
    (Usize.wrapping_sub a b).val=a.val-b.val := by
  rw [Usize.wrapping_sub_val_eq]
  rw [Nat.add_comm a.val (UScalar.size .Usize),Nat.add_sub_assoc h,Nat.add_mod]
  simp only [Nat.mod_self,Nat.zero_add]
  apply Nat.mod_eq_of_lt
  exact lt_of_le_of_lt (Nat.sub_le _ _) a.hBounds
#print axioms sub_small
end R1Z.PV_RunJoin_WeightRowCounters47
