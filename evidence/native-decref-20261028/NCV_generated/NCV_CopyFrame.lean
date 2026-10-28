import KMX_CopyMeaning
import NBX_SequenceDomains
set_option autoImplicit false
namespace NCV_CopyFrame

theorem commute {A : Type} (left right old : Nat → A) (a an b bn : Nat)
    (separate : a+an ≤ b ∨ b+bn ≤ a) :
    KMX_CopyMeaning.loop right (KMX_CopyMeaning.loop left old a an) b bn=
      KMX_CopyMeaning.loop left (KMX_CopyMeaning.loop right old b bn) a an := by
  funext k
  simp only [KMX_CopyMeaning.loop_spec]
  by_cases ha : a ≤ k ∧ k<a+an
  · have hb : ¬(b ≤ k ∧ k<b+bn) := by omega
    simp only [ha,hb,ite_true,ite_false]
  · by_cases hb : b ≤ k ∧ k<b+bn <;> simp only [ha,hb,ite_true,ite_false]

theorem row_windows {A : Type} (read old : Nat → A) (i j : Nat) (ordered : i<j) :
    KMX_CopyMeaning.loop read (KMX_CopyMeaning.loop read old (320+8*i) 8) (320+8*j) 8=
      KMX_CopyMeaning.loop read (KMX_CopyMeaning.loop read old (320+8*j) 8) (320+8*i) 8 := by
  apply commute
  left
  exact NBX_SequenceDomains.disjoint 320 i j ordered

theorem window_association {A : Type} (window original old : Nat → A) (off width k : Nat)
    (same : ∀ j, j<width → window j=original (off+j)) :
    KMX_CopyMeaning.loop window old 0 width k=
      if k<width then original (off+k) else old k := by
  rw [KMX_CopyMeaning.copy_prefix]
  split
  · rename_i h
    rw [same k h]
  · rfl

/-- Source bytes outside the selected field retain their original values.
Pointer validity/non-overlap and actual caller association remain native gates. -/
theorem outside {A : Type} (read old : Nat → A) (off width k : Nat)
    (separate : k<off ∨ off+width ≤ k) :
    KMX_CopyMeaning.loop read old off width k=old k :=
  KMX_CopyMeaning.copy_frame read old off width k separate

#print axioms commute
#print axioms row_windows
#print axioms window_association
#print axioms outside
end NCV_CopyFrame
