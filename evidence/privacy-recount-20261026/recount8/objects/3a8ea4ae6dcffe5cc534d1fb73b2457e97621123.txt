import R1Z.ProverCommitInterpolationIndices48
import R1Z.PV_RunJoin_MergeLoop35
import R1Z.ProverCommitInterpolationSchedule48
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InterpolationCounters38
open Aeneas Aeneas.Std
open ProverCommitInterpolationSchedule48

theorem cast32 (i : Usize) (hi : i.val≤28) :
    UScalar.cast .U32 (UScalar.cast .U8 i)=UScalar.cast .U32 i := by scalar_tac

theorem increment (i : Usize) (hi : i.val<28) :
    UScalar.cast .U8 (Usize.wrapping_add i 1#usize)=
      U8.wrapping_add (UScalar.cast .U8 i) 1#u8 := by
  have inc : (Usize.wrapping_add i 1#usize).val=i.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    change (i.val+1)%UScalar.size .Usize=i.val+1
    apply Nat.mod_eq_of_lt
    have big := (28#usize).hSize
    change 28<UScalar.size .Usize at big
    omega
  have cv : (UScalar.cast .U8 i).val=i.val := by scalar_tac
  have ci : (UScalar.cast .U8 (Usize.wrapping_add i 1#usize)).val=i.val+1 := by
    have small : (Usize.wrapping_add i 1#usize).val<256 := by rw [inc];omega
    have castval : (UScalar.cast .U8 (Usize.wrapping_add i 1#usize)).val=
        (Usize.wrapping_add i 1#usize).val := by scalar_tac
    rw [castval,inc]
  apply UScalar.eq_of_val_eq
  rw [ci,U8.wrapping_add_val_eq,cv,ProverCommitInterpolationIndices48.size_u8]
  change i.val+1=(i.val+1)%256
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem decrement (left : U8) (n : Nat) (hl : left.val=n+1) :
    (U8.wrapping_sub left 1#u8).val=n := by
  rw [ProverCommitBasisCounter47.sub_one left (by omega)]
  omega

theorem extend_room (i j d : Nat) (hi : i<28) (hj : j<28)
    (hd : d=degree i j) (different : i≠j) : d+2≤28 := by
  unfold degree at hd
  split at hd <;> omega

#print axioms cast32
#print axioms increment
#print axioms decrement
#print axioms extend_room
end R1Z.PV_RunJoin_InterpolationCounters38
