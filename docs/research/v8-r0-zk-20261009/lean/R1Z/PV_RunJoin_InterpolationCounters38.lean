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
      U8.wrapping_add (UScalar.cast .U8 i) 1#u8 := by scalar_tac

theorem decrement (left : U8) (n : Nat) (hl : left.val=n+1) :
    (U8.wrapping_sub left 1#u8).val=n := by scalar_tac

theorem extend_room (i j d : Nat) (hi : i<28) (hj : j<28)
    (hd : d=degree i j) (different : i≠j) : d+2≤28 := by
  unfold degree at hd
  split at hd <;> omega

#print axioms cast32
#print axioms increment
#print axioms decrement
#print axioms extend_room
end R1Z.PV_RunJoin_InterpolationCounters38
