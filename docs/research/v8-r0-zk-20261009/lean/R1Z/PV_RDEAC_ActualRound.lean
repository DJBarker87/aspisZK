import R1Z.PV_RDEA_ActualDigitLookup
import R1Z.PV_RDEAC_AppendSimulation
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_ActualRound
variable [ExternalTypes] [ExternalFuns]

def digits (digest : Array U8 32#usize) (i : Usize) : Result (Str × Str) := do
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
    ok (high,low)

theorem factor (digest : Array U8 32#usize) (s : String) (i : Usize) :
    PV_RDEA_ActualNameLoop.round digest s i = (do
      let (high,low) ← digits digest i
      let next ← ExternalFuns.op31 s high
      ExternalFuns.op31 next low) := by
  simp only [PV_RDEA_ActualNameLoop.round, digits, bind_assoc, bind_tc_ok]

#print Std.U8.wrapping_shr
#print UScalar.cast
#print UScalar.and
#print axioms factor
end R1Z.PV_RDEAC_ActualRound
