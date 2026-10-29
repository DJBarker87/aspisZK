import R1Z.PV_RunJoin_CircleRawSampler52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_SamplerCounters54

theorem sub_one (left : Usize) (positive : 0<left.val) :
    (Usize.wrapping_sub left 1#usize).val=left.val-1 := by
  rw [Usize.wrapping_sub_val_eq]
  have one : (1#usize).val=1 := rfl
  rw [one]
  have bound := left.hSize
  have size : 0<UScalar.size .Usize := by scalar_tac
  have shift : left.val+(UScalar.size .Usize-1)=(left.val-1)+UScalar.size .Usize := by omega
  rw [shift,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]

theorem increment (i : Usize) (small : i.val<32) :
    (Usize.wrapping_add i 1#usize).val=i.val+1 := by
  rw [Usize.wrapping_add_val_eq]
  change (i.val+1)%UScalar.size .Usize=i.val+1
  apply Nat.mod_eq_of_lt
  have hsize : 2^32≤UScalar.size .Usize := by
    rw [UScalar.size_def]
    exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits
  omega
#print axioms sub_one
#print axioms increment
end R1Z.PV_RunJoin_SamplerCounters54
