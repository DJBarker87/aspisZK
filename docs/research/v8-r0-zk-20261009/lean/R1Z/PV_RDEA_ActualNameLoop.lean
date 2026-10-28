import R1Z.PV_RDEA_ActualReservation
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEA_ActualNameLoop
variable [ExternalTypes] [ExternalFuns]

/-- Exact nonrecursive portion of the extracted reservation-name body. -/
def round (digest : Array U8 32#usize) (name1 : String) (i : Usize) : Result String := do
    let byte ← Array.index_usize digest i
    let i1 ← Aeneas.Std.lift (Std.U8.wrapping_shr byte 4#u32)
    let i2 ← Aeneas.Std.lift (UScalar.cast .Usize i1)
    let high ←
      Array.index_usize
        (Array.make 16#usize [
          toStr "0" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "1" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "2" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "3" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "4" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "5" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]),
          toStr "6" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "7" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "8" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "9" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "a" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "b" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]),
          toStr "c" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "d" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "e" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "f" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits])
          ]) i2
    let i3 ← Aeneas.Std.lift (byte &&& 15#u8)
    let i4 ← Aeneas.Std.lift (UScalar.cast .Usize i3)
    let low ←
      Array.index_usize
        (Array.make 16#usize [
          toStr "0" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "1" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "2" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "3" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "4" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "5" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]),
          toStr "6" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "7" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "8" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "9" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "a" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "b" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]),
          toStr "c" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "d" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "e" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits]), toStr "f" (by rw [String.size_toByteArray]; change 1 ≤ U32.max; norm_num [U32.max,U32.numBits])
          ]) i4
    let name2 ← alloc.string.String.push_str name1 high
    let name3 ← alloc.string.String.push_str name2 low
    ok name3

def finite (digest : Array U8 32#usize) : Nat → String → Usize → Result String
  | 0,acc,_ => ExternalFuns.op31 acc PV_RDEA_ActualReservation.suffixText
  | n+1,acc,i => do
    let next ← round digest acc i
    finite digest n next (Usize.wrapping_add i 1#usize)

theorem step (digest : Array U8 32#usize) (acc : String) (i : Usize)
    (go : i≠32#usize) :
    aspis_prover.state_only_entropy.reservation_name digest acc i = (do
      let next ← round digest acc i
      aspis_prover.state_only_entropy.reservation_name digest next (Usize.wrapping_add i 1#usize)) := by
  rw [aspis_prover.state_only_entropy.reservation_name.eq_def]
  simp only [go,if_false,round,lift,bind_tc_ok,bind_assoc]

#print axioms step
end R1Z.PV_RDEA_ActualNameLoop
