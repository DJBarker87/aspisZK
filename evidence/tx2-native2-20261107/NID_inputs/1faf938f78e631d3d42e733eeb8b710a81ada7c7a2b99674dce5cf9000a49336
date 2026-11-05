import NID_RawWindowFrame
import KMX_CopyMeaning
set_option autoImplicit false
namespace NID_KmxComposition

def copyFour {A : Type} (src dst : Nat → A) (row : Nat) : Nat → A :=
 KMX_CopyMeaning.loop src
  (KMX_CopyMeaning.loop src
   (KMX_CopyMeaning.loop src
    (KMX_CopyMeaning.loop src dst (4*row) 1) (4*row+1) 1) (4*row+2) 1) (4*row+3) 1

/-- The four disjoint native u64 windows compose to the prescribed KMX row
copy, on arbitrary source/destination prestate, including every framed cell. -/
theorem copy_four_spec {A : Type} (src dst : Nat → A) (row k : Nat) :
 copyFour src dst row k = if 4*row≤k ∧ k<4*row+4 then src k else dst k := by
 simp only [copyFour,KMX_CopyMeaning.loop_spec]
 split_ifs <;> first | rfl | omega

theorem copy_four_frame {A : Type} (src dst : Nat → A) (row k : Nat)
 (outside : k<4*row ∨ 4*row+4≤k) : copyFour src dst row k=dst k := by
 rw [copy_four_spec,if_neg]
 omega

def rows {A : Type} (src dst : Nat → A) : Nat → Nat → A
 | 0 => dst
 | n+1 => copyFour src (rows src dst n) n

/-- Symbolic induction over rows; never kernel-reduce a concrete256-cell
copy recurrence. Pointer validity/non-overlap/allocation remain KMX domains. -/
theorem rows_spec {A : Type} (src dst : Nat → A) (count k : Nat) :
 rows src dst count k = if k<4*count then src k else dst k := by
 induction count with
 | zero => simp only [rows,Nat.mul_zero,Nat.not_lt_zero,if_false]
 | succ n ih =>
   change copyFour src (rows src dst n) n k=_
   rw [copy_four_spec,ih]
   split_ifs <;> first | rfl | omega

theorem all64 {A : Type} (src dst : Nat → A) (k : Nat) :
 rows src dst 64 k=KMX_CopyMeaning.loop src dst 0 256 k := by
 rw [rows_spec,KMX_CopyMeaning.copy_prefix]

/-- Any original row/limb is supplied by the same source after all64 copies;
no other row is fixed and no success of an enclosing query is assumed. -/
theorem selected {A : Type} (src dst : Nat → A) (row limb : Nat)
 (r : row<64) (j : limb<4) :
 rows src dst 64 (4*row+limb)=src (4*row+limb) := by
 rw [all64,KMX_CopyMeaning.copy_prefix,if_pos]
 omega
#print axioms copy_four_spec
#print axioms copy_four_frame
#print axioms rows_spec
#print axioms all64
#print axioms selected
end NID_KmxComposition
