import RPx_Deployed
import NCD_KMX_CopyMeaning
set_option autoImplicit false
namespace AspisR1.NCL_SaveWindows

/-- Value plane for the checkpoint copy at an arbitrary actual account base.
Validity, disjointness and native association are NOT supplied by this law. -/
def copy {α : Type} (saved before : Nat → α) (base : Nat) : Nat → α :=
  KMX_CopyMeaning.loop (fun k => saved (k-base)) before base 1768

theorem saved_byte {α : Type} (saved before : Nat → α) (base i : Nat)
    (inside : i<1768) : copy saved before base (base+i)=saved i := by
  unfold copy
  rw [KMX_CopyMeaning.loop_spec,if_pos (by omega)]
  congr 1
  omega

theorem outside {α : Type} (saved before : Nat → α) (base k : Nat)
    (frame : k<base ∨ base+1768≤k) : copy saved before base k=before k :=
  KMX_CopyMeaning.copy_frame _ _ base 1768 k frame

/-- Snapshot and write must refer to disjoint actual regions; length equality
alone is insufficient. The theorem retains the pre-write byte at every
coordinate of the original proof/public region. -/
theorem disjoint_input {α : Type} (saved before : Nat → α) (base input size : Nat)
    (apart : input+size≤base ∨ base+1768≤input) :
    ∀ i, i<size → copy saved before base (input+i)=before (input+i) := by
  intro i hi
  apply outside
  omega

/-- A later allocator cleanup is composed only through its actual read/write
frame on the SAME copied state. It cannot select a different checkpoint. -/
theorem cleanup_keeps_saved {α : Type} (saved before after : Nat → α) (base : Nat)
    (frame : ∀ i, i<1768 → after (base+i)=copy saved before base (base+i)) :
    ∀ i, i<1768 → after (base+i)=saved i := by
  intro i hi
  exact (frame i hi).trans (saved_byte saved before base i hi)

#print axioms saved_byte
#print axioms outside
#print axioms disjoint_input
#print axioms cleanup_keeps_saved
end AspisR1.NCL_SaveWindows
