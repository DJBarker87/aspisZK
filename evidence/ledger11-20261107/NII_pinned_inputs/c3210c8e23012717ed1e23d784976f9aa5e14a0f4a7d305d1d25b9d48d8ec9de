import NHD_CopyWindows
set_option autoImplicit false
namespace NHD_SnapshotWindows

/-- Physical-address interpretation of the KMX indexed value copy.
Validity, allocation and native call association remain external obligations. -/
def copy {α : Type} (heap : Nat → α) (source destination count : Nat) : Nat → α :=
  fun address => if destination ≤ address ∧ address < destination+count
    then KMX_CopyMeaning.loop (fun k => heap (source+k))
      (fun k => heap (destination+k)) 0 count (address-destination)
    else heap address

theorem byte {α : Type} (heap : Nat → α) (source destination count offset : Nat)
    (inside : offset < count) :
    copy heap source destination count (destination+offset) = heap (source+offset) := by
  have interval : destination ≤ destination+offset ∧ destination+offset < destination+count := by omega
  simp only [copy,if_pos interval,Nat.add_sub_cancel_left,KMX_CopyMeaning.copy_prefix,if_pos inside]

theorem outside {α : Type} (heap : Nat → α) (source destination count address : Nat)
    (frame : address < destination ∨ destination+count ≤ address) :
    copy heap source destination count address = heap address := by
  have out : ¬ (destination ≤ address ∧ address < destination+count) := by omega
  simp only [copy,if_neg out]

theorem source_preserved {α : Type} (heap : Nat → α) (source destination count offset : Nat)
    (separate : source+count ≤ destination ∨ destination+count ≤ source)
    (inside : offset < count) :
    copy heap source destination count (source+offset) = heap (source+offset) := by
  apply outside
  omega

/-- All output bytes and source/frame cells follow pointwise; no sampled offset
or independently supplied output equality is promoted to a native theorem. -/
theorem full_frame {α : Type} (heap : Nat → α) (source destination count : Nat)
    (separate : source+count ≤ destination ∨ destination+count ≤ source) :
    (∀ offset, offset < count →
      copy heap source destination count (destination+offset) = heap (source+offset)) ∧
    (∀ offset, offset < count →
      copy heap source destination count (source+offset) = heap (source+offset)) ∧
    (∀ address, address < destination ∨ destination+count ≤ address →
      copy heap source destination count address = heap address) := by
  exact ⟨fun k h => byte heap source destination count k h,
    fun k h => source_preserved heap source destination count k separate h,
    fun k h => outside heap source destination count k h⟩

#print axioms byte
#print axioms outside
#print axioms source_preserved
#print axioms full_frame
end NHD_SnapshotWindows
