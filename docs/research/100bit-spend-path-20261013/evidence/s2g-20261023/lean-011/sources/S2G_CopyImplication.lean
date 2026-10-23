import S2C_CopyRegions

/-! The selected-coordinate Kani postcondition is a weakening of the existing
symbolic copy theorem. No native Heap representation is fabricated here. -/
set_option autoImplicit false
namespace AspisR1.S2G.CopyImplication
open S2Trust S2C

theorem selected_byte {F : Type} (heap : Heap F) (guard : Guard)
    (source : Nat → UInt8) (i : Nat) (expected : UInt8)
    (bound : i < 1768) (snapshot : expected = source i) :
    ((copyPrefix heap guard source 1768).payload guard.cell).contents i = expected := by
  rw [copy_exact_byte,if_pos bound,snapshot]

/-- Outside the destination's cell, even its complete payload is preserved.
The native Kani write-set is independently checked in its safe slice domain. -/
theorem other_cell {F : Type} (heap : Heap F) (guard : Guard)
    (source : Nat → UInt8) (cell : Nat) (separate : cell ≠ guard.cell) :
    (copyPrefix heap guard source 1768).payload cell = heap.payload cell :=
  copy_other_cell heap guard source 1768 cell separate

#print axioms selected_byte
#print axioms other_cell
end AspisR1.S2G.CopyImplication
