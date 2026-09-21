import AspisV8R17.WeightedScatter
import Mathlib.Data.ZMod.Basic

/-! First frozen source-model entry. Original active row 11 maps to
coefficient 100; selected column 6 is degree 24, channel B, alpha power 1.
No full source matrix is normalized. -/
set_option autoImplicit false
namespace AspisV8R17

theorem source_first_block_entry :
    sourceChord (1073741824 : ZMod 2147483647)
      (fun i => unitVector 97 i-2*unitVector 96 i) 13 11 (-7) 100 = 1073741827 := by
  rw [sourceChord_difference]
  rw [sourceChord_unit_odd _ 48 100 (by decide),
      sourceChord_unit_even _ 48 100 (by decide)]
  decide

#print axioms source_first_block_entry
end AspisV8R17
