import R1Z.PV_RunJoin_WeightCounters46
import R1Z.PV_RunJoin_WeightPointRows46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightRowCounters47
open Aeneas Aeneas.Std Result

theorem sub_small (a b : Usize) (h : b.val≤a.val) :
    (Usize.wrapping_sub a b).val=a.val-b.val := by
  have ha : a.val<UScalar.size .Usize := by
    rw [UScalar.size]
    exact a.hBounds
  have hb : b.val≤UScalar.size .Usize := by omega
  have he : a.val+(UScalar.size .Usize-b.val)=UScalar.size .Usize+(a.val-b.val) := by omega
  rw [Usize.wrapping_sub_val_eq,he,Nat.add_mod]
  simp only [Nat.mod_self,Nat.zero_add,Nat.mod_mod]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) ha)
#print axioms sub_small
end R1Z.PV_RunJoin_WeightRowCounters47
