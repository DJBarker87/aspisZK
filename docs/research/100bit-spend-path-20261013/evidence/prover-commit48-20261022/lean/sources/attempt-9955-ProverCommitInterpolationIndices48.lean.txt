import R1Z.ProverCommitInterpolationSchedule48
import R1Z.ProverCommitBasisCounter47
/-! Bounded source counters and base-field casts for the interpolation loop. -/
set_option autoImplicit false
namespace R1Z.ProverCommitInterpolationIndices48
open Aeneas Aeneas.Std Result

theorem size_u8 : UScalar.size .U8=256 := by rw [UScalar.size_def];rfl

theorem cast32_val (x : U8) : (UScalar.cast .U32 x).val=x.val := by scalar_tac

theorem cast32_canonical (x : U8) : ProverCommitM31Ops48.canonical (UScalar.cast .U32 x) := by
  change (UScalar.cast .U32 x).val < ProverCommitM31Ops48.P
  rw [cast32_val]
  have hx := x.hSize
  rw [size_u8] at hx
  have large : 256 < ProverCommitM31Ops48.P := by decide
  omega

theorem cast32_decode (x : U8) :
    ProverCommitM31Ops48.decode (UScalar.cast .U32 x)=(x.val : ProverCommitM31Ops48.M) := by
  change ((UScalar.cast .U32 x).val : ProverCommitM31Ops48.M)=_
  rw [cast32_val]

theorem add_val (x y : U8) (bound : x.val+y.val < 256) :
    (U8.wrapping_add x y).val=x.val+y.val := by
  rw [U8.wrapping_add_val_eq,size_u8]
  exact Nat.mod_eq_of_lt bound

theorem next_val (x : U8) (bound : x.val < 28) :
    (U8.wrapping_add x 1#u8).val=x.val+1 := by
  have one : (1#u8).val=1 := rfl
  rw [add_val x 1#u8 (by rw [one];omega),one]

#print axioms size_u8
#print axioms cast32_val
#print axioms cast32_canonical
#print axioms cast32_decode
#print axioms add_val
#print axioms next_val
end R1Z.ProverCommitInterpolationIndices48
