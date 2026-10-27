import R1Z.PV_CBL_DigestUpdateStep
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_DigestUpdateInvariant
set_option autoImplicit false
theorem eager (state : Array U32 8#usize) (blocks : U64) (buffer : Array U8 64#usize)
    (pos : Usize) (byte : U8) (hp : pos.val<64) :
    (PV_CBL_DigestUpdateStep.next state blocks buffer pos byte).2.2.2.val<64 := by
  have inc := PV_CBL_ArrayStep.increment pos 64#usize hp
  by_cases hc : Usize.wrapping_add pos 1#usize=64#usize
  · have hv : PV_CBL_DigestUpdateStep.next state blocks buffer pos byte =
        (PV_CBL_SoftByteSource.value state (buffer.set pos byte),
          U64.wrapping_add blocks 1#u64,buffer.set pos byte,0#usize) := by
      unfold PV_CBL_DigestUpdateStep.next
      rw [if_pos hc]
    calc
      _ = 0 := congrArg (fun q : PV_CBL_DigestUpdateStep.Snapshot => q.2.2.2.val) hv
      _ < 64 := by decide
  · have hv : PV_CBL_DigestUpdateStep.next state blocks buffer pos byte =
        (state,blocks,buffer.set pos byte,Usize.wrapping_add pos 1#usize) := by
      unfold PV_CBL_DigestUpdateStep.next
      rw [if_neg hc]
    have he : (Usize.wrapping_add pos 1#usize).val≠64 := by
      intro h
      apply hc
      apply UScalar.eq_of_val_eq
      exact h
    calc
      _ = (Usize.wrapping_add pos 1#usize).val :=
        congrArg (fun q : PV_CBL_DigestUpdateStep.Snapshot => q.2.2.2.val) hv
      _ < 64 := by omega
#print axioms eager
end R1Z.PV_CBL_DigestUpdateInvariant
