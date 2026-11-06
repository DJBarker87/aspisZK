import KMX_CopyMeaning
import NKQ_ArrayWindows
set_option autoImplicit false
namespace AspisR1.NLC_CopyFrames
open Aeneas Aeneas.Std
/-- Compose windows using the pinned KMX value law, never by unfolding the
copy loop. Pointer validity, allocation, layout and ownership are not inferred. -/
theorem copied_window {A : Type} (src dst : Nat → A) (start count index : Nat)
 (inside : start ≤ index ∧ index < start + count) :
 KMX_CopyMeaning.loop src dst start count index = src index := by
 rw [KMX_CopyMeaning.loop_spec,if_pos inside]

theorem retained_window {A : Type} (src dst : Nat → A) (start count index : Nat)
 (outside : index < start ∨ start + count ≤ index) :
 KMX_CopyMeaning.loop src dst start count index = dst index :=
 KMX_CopyMeaning.copy_frame src dst start count index outside

theorem disjoint_windows {A : Type} (first second original : Nat → A)
 (a na b nb index : Nat) (inFirst : a ≤ index ∧ index < a + na)
 (disjoint : a + na ≤ b ∨ b + nb ≤ a) :
 KMX_CopyMeaning.loop second (KMX_CopyMeaning.loop first original a na) b nb index = first index := by
 rw [KMX_CopyMeaning.copy_frame]
 · exact copied_window first original a na index inFirst
 · omega

/-- Pointwise field windows reconstruct the complete fixed-array value. This
is a value statement; no byte identity is derived from an address. -/
theorem array_windows {A : Type} {n : Usize} (source actual : Array A n)
 (windows : ∀ i (inside : i < n.val),
   NKQ_ArrayWindows.cell actual i inside = NKQ_ArrayWindows.cell source i inside) : actual = source :=
 NKQ_ArrayWindows.extensional actual source windows
#print axioms copied_window
#print axioms retained_window
#print axioms disjoint_windows
#print axioms array_windows
end AspisR1.NLC_CopyFrames
