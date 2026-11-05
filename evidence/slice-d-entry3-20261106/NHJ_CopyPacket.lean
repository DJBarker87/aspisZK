import NHD_SnapshotWindows
import NGL_BorrowFrame
set_option autoImplicit false
namespace NHJ_CopyPacket
open Aeneas.Std

/-- From the actual KMX one-window law and retained induction, every copied
byte is initialized. No copied output equality is an input. -/
theorem initialized (heap : Nat → Option U8) (source destination count : Nat)
    (sourceReady : ∀ i, i < count → ∃ byte, heap (source+i) = some byte) :
    ∀ i, i < count → ∃ byte,
      NHD_SnapshotWindows.copy heap source destination count (destination+i) = some byte := by
  intro i inside
  obtain ⟨byte,ready⟩ := sourceReady i inside
  exact ⟨byte,(NHD_SnapshotWindows.byte heap source destination count i inside).trans ready⟩

/-- Byte interpretation of the full copied allocation; this composes the
pointwise windows without evaluating a count-sized recurrence. -/
theorem contents (heap : Nat → U8) (source destination count : Nat) :
    NGL_BorrowFrame.contents (NHD_SnapshotWindows.copy heap source destination count)
      destination count = NGL_BorrowFrame.contents heap source count := by
  unfold NGL_BorrowFrame.contents
  apply List.map_congr_left
  intro i member
  exact NHD_SnapshotWindows.byte heap source destination count i (List.mem_range.mp member)

theorem source_contents (heap : Nat → U8) (source destination count : Nat)
    (separate : source+count ≤ destination ∨ destination+count ≤ source) :
    NGL_BorrowFrame.contents (NHD_SnapshotWindows.copy heap source destination count)
      source count = NGL_BorrowFrame.contents heap source count :=
  NGL_BorrowFrame.preserved heap _ source count
    (fun i inside => NHD_SnapshotWindows.source_preserved heap source destination count i separate inside)
#print axioms initialized
#print axioms contents
#print axioms source_contents
end NHJ_CopyPacket
