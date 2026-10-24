import Port4B_Prepared
import Port4B_TailRun

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_Bounds
open Aeneas Aeneas.Std Result

/-- Actual native split arithmetic: both counts and bases are small. -/
theorem count (batch : Usize) :
    (Port4B_TreeCuts.count batch).val=(if batch=0#usize then 10 else 12) ∧
    (Port4B_TreeCuts.lo batch).val=(if batch.val=0 then 0 else 10) := by
  have cap : 22<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
  by_cases zero : batch=0#usize
  · subst batch
    constructor
    · change (Usize.wrapping_sub 10#usize 0#usize).val=10
      rw [Usize.wrapping_sub_val_eq]
      change (10+(UScalar.size .Usize-0))%UScalar.size .Usize=10
      rw [Nat.sub_zero,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    · rfl
  · have nonzero : batch.val≠0 := by intro h;exact zero (UScalar.eq_of_val_eq h)
    constructor
    · simp only [Port4B_TreeCuts.count,Port4B_TreeCuts.hi,Port4B_TreeCuts.lo,if_neg zero]
      rw [Usize.wrapping_sub_val_eq]
      change (22+(UScalar.size .Usize-10))%UScalar.size .Usize=12
      rw [show 22+(UScalar.size .Usize-10)=12+UScalar.size .Usize by omega,
        Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    · simp only [Port4B_TreeCuts.lo,if_neg zero,if_neg nonzero];rfl

theorem slot (batch kind : Usize) (b : batch.val<2) (k : kind.val<3) :
    (Port4B_TreeCuts.slot batch kind).val=3*batch.val+kind.val := by
  have mul := Port3_Wrapping.wrap_mul_value 3#usize batch (by change 3*batch.val≤4096;omega)
  unfold Port4B_TreeCuts.slot
  rw [Port3_Wrapping.wrap_add_value _ _ (by rw [mul];change 3*batch.val+kind.val≤4096;omega),mul]
  rfl

#print axioms count
#print axioms slot
end AspisR1.Port4B_Bounds
end
