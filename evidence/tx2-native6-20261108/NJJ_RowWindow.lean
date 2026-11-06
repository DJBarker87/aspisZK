import NJC_CopyFrame
set_option autoImplicit false
namespace NJJ_RowWindow
/-- One four-limb native row store at an arbitrary row offset. KMX is the
supplied value law; validity, fresh ownership and nonoverlap are established
by the enclosing native cut and CLOSED filled child, not assumed here. -/
def write {A : Type} (before : Nat → A) (i : Nat) (row : Nat → A) : Nat → A :=
 KMX_CopyMeaning.loop (fun j=>row (j-4*i)) before (4*i) 4

theorem cell {A : Type} (before row : Nat → A) (i limb : Nat) (inside : limb<4) :
 write before i row (4*i+limb)=row limb := by
 unfold write
 rw [KMX_CopyMeaning.loop_spec,if_pos (by omega)]
 simp only [Nat.add_sub_cancel_left]

theorem frame {A : Type} (before row : Nat → A) (i index : Nat)
 (outside : index<4*i ∨ 4*i+4≤index) :
 write before i row index=before index :=
 NJC_CopyFrame.frame _ _ _ _ _ outside

/-- A distinct row is untouched; this is the whole-buffer lift after K015,
not another execution of its timed-out symbolic64-vector shape. -/
theorem other {A : Type} (before row : Nat → A) (i j limb : Nat)
 (different : i≠j) (inside : limb<4) :
 write before i row (4*j+limb)=before (4*j+limb) := by
 apply frame
 omega

theorem composed {A : Type} (before first second : Nat → A) (i j limb : Nat)
 (different : i≠j) (inside : limb<4) :
 write (write before i first) j second (4*i+limb)=first limb := by
 rw [other _ _ j i limb (Ne.symm different) inside,cell _ _ i limb inside]

#print axioms cell
#print axioms frame
#print axioms other
#print axioms composed
end NJJ_RowWindow
