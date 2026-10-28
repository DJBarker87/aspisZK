import KMX_CopyMeaning
import NCM_WindowImage

set_option autoImplicit false
namespace AspisR1.NCM_KMXWindows

/-- Compose adjacent copy windows over the exact KMX indexed-write value law.
Pointer validity, disjoint ownership and source association remain external. -/
theorem adjacent {α : Type} (src dst : Nat → α) (start a b : Nat) :
    KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop src dst start a) (start+a) b =
      KMX_CopyMeaning.loop src dst start (a+b) := by
  funext k
  simp only [KMX_CopyMeaning.loop_spec]
  by_cases left : start ≤ k ∧ k < start+a
  · have right : ¬(start+a ≤ k ∧ k < start+a+b) := by omega
    have all : start ≤ k ∧ k < start+(a+b) := by omega
    simp only [if_neg right,if_pos left,if_pos all]
  · by_cases right : start+a ≤ k ∧ k < start+a+b
    · have all : start ≤ k ∧ k < start+(a+b) := by omega
      simp only [if_pos right,if_pos all]
    · have all : ¬(start ≤ k ∧ k < start+(a+b)) := by omega
      simp only [if_neg right,if_neg left,if_neg all]

/-- Two disjoint physical destinations commute, including every untouched byte.
This is a value theorem, not a claim about aliasing native pointers. -/
theorem disjoint {α : Type} (src other dst : Nat → α) (a n b m : Nat)
    (apart : a+n ≤ b ∨ b+m ≤ a) :
    KMX_CopyMeaning.loop src (KMX_CopyMeaning.loop other dst b m) a n =
      KMX_CopyMeaning.loop other (KMX_CopyMeaning.loop src dst a n) b m := by
  funext k
  simp only [KMX_CopyMeaning.loop_spec]
  by_cases left : a ≤ k ∧ k < a+n
  · have right : ¬(b ≤ k ∧ k < b+m) := by omega
    simp only [if_pos left,if_neg right]
  · simp only [if_neg left]

/-- The native arbitrary-offset window plus KMX frame determines all cells. -/
theorem window_frame {α : Type} (actual src old : Nat → α) (start count : Nat)
    (inside : ∀ k, start ≤ k → k < start+count → actual k=src k)
    (frame : ∀ k, k<start ∨ start+count≤k → actual k=old k) :
    actual = KMX_CopyMeaning.loop src old start count := by
  funext k
  rw [KMX_CopyMeaning.loop_spec]
  by_cases active : start ≤ k ∧ k < start+count
  · rw [if_pos active];exact inside k active.1 active.2
  · rw [if_neg active];exact frame k (by omega)

#print axioms adjacent
#print axioms disjoint
#print axioms window_frame
end AspisR1.NCM_KMXWindows
