import Aeneas
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace PCVB_R23
def r23 (left : Std.U64) (right : Std.U64) : Result Std.U64 := do
  let i ← lift (core.convert.num.FromU64U32.from core.num.U32.MAX)
  if left <= i
  then
    let i1 ← lift (core.convert.num.FromU64U32.from core.num.U32.MAX)
    if right <= i1
    then
      let i2 ← lift (UScalar.cast .U32 left)
      let i3 ← lift (core.convert.num.FromU64U32.from i2)
      let i4 ← lift (UScalar.cast .U32 right)
      let i5 ← lift (core.convert.num.FromU64U32.from i4)
      i3 * i5
    else left * right
  else left * right

theorem hmaxA : (core.convert.num.FromU64U32.from core.num.U32.MAX).val = 4294967295 := by
  rw [core.convert.num.FromU64U32.from_val_eq]; rfl
theorem hmaxB : (core.convert.num.FromU64U32.from core.num.U32.MAX).val = 4294967295 := by
  rw [core.convert.num.FromU64U32.from_val_eq]; scalar_tac
theorem hmaxC : (core.convert.num.FromU64U32.from core.num.U32.MAX).val = 4294967295 := by
  rw [core.convert.num.FromU64U32.from_val_eq]; simp [core.num.U32.MAX]; scalar_tac

theorem hcastF (l : Std.U64) (h : l.val ≤ 4294967295) :
    core.convert.num.FromU64U32.from (UScalar.cast .U32 l) = l := by
  apply UScalar.eq_imp
  rw [core.convert.num.FromU64U32.from_val_eq, UScalar.cast_val_eq, UScalarTy.U32_numBits_eq]
  exact Nat.mod_eq_of_lt (by omega)

theorem r23_eq (l r : Std.U64) : r23 l r = l * r := by
  unfold r23
  simp only [lift, bind_tc_ok]
  split_ifs with h1 h2
  · have a1 := (UScalar.le_equiv _ _).mp h1
    have a2 := (UScalar.le_equiv _ _).mp h2
    rw [hmaxB] at a1 a2
    rw [hcastF l a1, hcastF r a2]
  · rfl
  · rfl
end PCVB_R23
