import ExtractedMaskQmPackBase4Arithmetic
import ExtractedMaskQM31Exact

/-! Pure exact-tower algebra for the actual per-cell selector multiplication:
when each source QM31 is decoded to `selector * input`, the four-cell pack is
scaled by that same selector. This is the algebraic bridge used after the
source loop and before the existing four-cell pack adapter. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLanePackScale

open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskQmPackBase4Arithmetic

abbrev QM := AspisR1.ExtractedMaskQM31Exact.CurrentQM

/-- The exact four-limb tower pack distributes over a common left scalar. -/
theorem mathematicalPack_mul_left
    (selector : QM) (values source : Fin 4 → QM)
    (h : ∀ j : Fin 4, decode (values j) = decode selector * decode (source j)) :
    mathematicalPack values = decode selector * mathematicalPack source := by
  unfold mathematicalPack
  rw [h 0, h 1, h 2, h 3]
  ring

#print axioms mathematicalPack_mul_left
end AspisR1.SelectorValueLanePackScale
