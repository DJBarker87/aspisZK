import NHM_ArrayPreserve
set_option autoImplicit false
namespace NHM_FactoredFrames
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev Cells := Array NE 4#usize

def first (a : Cells) (x y : NE) : Cells :=
 NHI_ArrayCells.put (NHI_ArrayCells.put a 0#usize x) 1#usize y

def second (a : Cells) (x y z : NE) : Cells :=
 NHI_ArrayCells.put (NHI_ArrayCells.put (NHI_ArrayCells.put a 1#usize x) 2#usize y) 3#usize z

theorem first_frame (a : Cells) (x y : NE) (i : Nat) (h0 : i≠0) (h1 : i≠1) :
 (first a x y).val[i]?=a.val[i]? := by
 unfold first
 rw [NHI_ArrayCells.frame _ 1#usize _ i h1,NHI_ArrayCells.frame _ 0#usize _ i h0]

theorem second_frame (a : Cells) (x y z : NE) (i : Nat)
 (h1 : i≠1) (h2 : i≠2) (h3 : i≠3) : (second a x y z).val[i]?=a.val[i]? := by
 unfold second
 rw [NHI_ArrayCells.frame _ 3#usize _ i h3,NHI_ArrayCells.frame _ 2#usize _ i h2,NHI_ArrayCells.frame _ 1#usize _ i h1]

/-- Source-order two-side frame: the second side preserves the first side's
slot0 and the first side preserves slots2/3 for the second side's writes. -/
theorem combined (a : Cells) (a0 a1 b1 b2 b3 : NE) :
 (second (first a a0 a1) b1 b2 b3).val[0]?=some a0 := by
 rw [second_frame _ _ _ _ 0 (by decide) (by decide) (by decide)]
 unfold first
 rw [NHI_ArrayCells.frame _ 1#usize _ 0 (by decide)]
 exact NHI_ArrayCells.selected a 0#usize a0 (by decide)

#print axioms first_frame
#print axioms second_frame
#print axioms combined
end NHM_FactoredFrames
