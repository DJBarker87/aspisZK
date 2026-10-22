import S9AfterScalarTermSumsV1
import S9SideZeroTailRootV1
import S9SideOneTailRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9AfterSumsTailDispatchV1

open AspisR1S9HelperP6

local instance concreteOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31
abbrev U := Std.Usize

private theorem result_bind_assoc {α β γ : Type} (m : Result α)
    (f : α → Result β) (g : β → Result γ) :
    (do let y ← (do let x ← m; f x); g y) =
      (do let x ← m; let y ← f x; g y) := by
  cases m <;> rfl

theorem afterSums_side_zero
    (ap1 weights0 : W) (iterNext : core.ops.range.Range U)
    (low first2 first3 all : field.WideExact) (q4 q16 : Q) :
    @AspisR1S9AfterScalarTermSumsV1.afterSums
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      ap1 0#usize iterNext weights0 low first2 first3 all q4 q16 =
    (do
      let out ← AspisR1.S9SideZeroTailRootV1.sideZeroTail
        weights0 low first3 all q16
      ok (cont (iterNext,out))) := by
  unfold AspisR1S9AfterScalarTermSumsV1.afterSums
  rw [if_pos (show (0#usize : U) = 0#usize from rfl)]
  simp only [AspisR1.S9SideZeroTailRootV1.sideZeroTail, result_bind_assoc, bind_tc_ok]

theorem afterSums_side_one
    (ap1 weights0 : W) (iterNext : core.ops.range.Range U)
    (low first2 first3 all : field.WideExact) (q4 q16 : Q) :
    @AspisR1S9AfterScalarTermSumsV1.afterSums
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      ap1 1#usize iterNext weights0 low first2 first3 all q4 q16 =
    (do
      let out ← AspisR1.S9SideOneTailRootV1.sideOneTail
        weights0 ap1 low all first2 q4 q16
      ok (cont (iterNext,out))) := by
  have hne : (1#usize : U) ≠ 0#usize := by
    intro h
    have hval := congrArg UScalar.val h
    have heq : (1 : Nat) = 0 := by simpa using hval
    omega
  unfold AspisR1S9AfterScalarTermSumsV1.afterSums
  rw [if_neg hne]
  simp only [AspisR1.S9SideOneTailRootV1.sideOneTail, result_bind_assoc, bind_tc_ok]

#print axioms afterSums_side_zero
#print axioms afterSums_side_one

end AspisR1S9AfterSumsTailDispatchV1
