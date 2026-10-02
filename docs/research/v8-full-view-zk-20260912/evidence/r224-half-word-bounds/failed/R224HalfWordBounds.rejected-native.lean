import Mathlib.Tactic
import Std.Tactic.BVDecide

/-! Finite-width predecessor for the selected M31 half operation: rotate
its low 31 bits, retaining the canonical bound and exact unreduced double.
No source half-method correspondence is asserted here. -/
set_option autoImplicit false
namespace AspisV8R19.R224HalfWordBounds

def halfWord (w : BitVec 32) : BitVec 32 :=
  (w >>> 1) ||| ((w &&& 1) <<< 30)

theorem canonical (w : BitVec 32) (h : w < 2147483647#32) :
    halfWord w < 2147483647#32 := by
  unfold halfWord
  bv_decide

theorem double_word (w : BitVec 32) (h : w < 2147483647#32) :
    halfWord w + halfWord w =
      w + (if w &&& 1 = 0 then 0 else 2147483647#32) := by
  unfold halfWord
  bv_decide

#print axioms canonical
#print axioms double_word
end AspisV8R19.R224HalfWordBounds
