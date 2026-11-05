import KMX_CopyMeaning
import NIO_Nested
set_option autoImplicit false
namespace NIO_Windows

def window {α : Type} (src dst : Nat → Nat → α) (cell offset : Nat) : Nat → Nat → α :=
  fun c i => if c = cell then KMX_CopyMeaning.loop (src c) (dst c) offset 1 i else dst c i

theorem selected_value {α : Type} (src dst : Nat → Nat → α) (c i : Nat) :
    window src dst c i c i = src c i := by
  simp [window,KMX_CopyMeaning.loop_spec]
#print axioms selected_value

theorem other_cell_frame {α : Type} (src dst : Nat → Nat → α)
    (c d i j : Nat) (ne : d ≠ c) : window src dst c i d j = dst d j := by
  simp [window,ne]
#print axioms other_cell_frame

theorem other_offset_frame {α : Type} (src dst : Nat → Nat → α)
    (c i j : Nat) (ne : j ≠ i) : window src dst c i c j = dst c j := by
  simp only [window,if_pos,KMX_CopyMeaning.loop_spec]
  have outside : ¬ (i ≤ j ∧ j < i+1) := by omega
  simp only [if_neg outside]
#print axioms other_offset_frame

/-- Independent physical-cell windows commute on the entire payload carrier. -/
theorem distinct_cells_commute {α : Type} (src dst : Nat → Nat → α)
    (c d i j : Nat) (ne : c ≠ d) :
    window src (window src dst c i) d j = window src (window src dst d j) c i := by
  funext e k
  by_cases hc : e = c <;> by_cases hd : e = d
  · exact False.elim (ne (hc.symm.trans hd))
  · simp [window,hc,hd,KMX_CopyMeaning.loop_spec]
  · simp [window,hc,hd,KMX_CopyMeaning.loop_spec]
  · simp [window,hc,hd]
#print axioms distinct_cells_commute

/-- The pinned KMX induction supplies arbitrary copy widths; no concrete 384/192
buffer is normalized in the kernel. -/
theorem full_copy_value {α : Type} (src dst : Nat → α) (width k : Nat)
    (inside : k < width) : KMX_CopyMeaning.loop src dst 0 width k = src k := by
  rw [KMX_CopyMeaning.copy_prefix]
  exact if_pos inside
#print axioms full_copy_value

theorem full_copy_frame {α : Type} (src dst : Nat → α) (width k : Nat)
    (outside : width ≤ k) : KMX_CopyMeaning.loop src dst 0 width k = dst k := by
  rw [KMX_CopyMeaning.copy_prefix]
  exact if_neg (by omega)
#print axioms full_copy_frame
end NIO_Windows
