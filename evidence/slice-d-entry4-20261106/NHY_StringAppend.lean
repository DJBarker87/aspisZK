import NHD_SnapshotWindows
set_option autoImplicit false
namespace NHY_StringAppend

def append {α : Type} (heap : Nat → α) (source base old count : Nat) : Nat → α :=
 NHD_SnapshotWindows.copy heap source (base+old) count

def view {α : Type} (heap : Nat → α) (base count : Nat) : List α :=
 (List.range count).map (fun k => heap (base+k))

/-- Appending one literal leaves every prefix byte unchanged. -/
theorem prefix_frame {α : Type} (heap : Nat → α) (source base old count k : Nat)
    (inside : k < old) :
    append heap source base old count (base+k) = heap (base+k) := by
  apply NHD_SnapshotWindows.outside
  omega

/-- Every appended byte follows from the existing KMX value law. -/
theorem appended_byte {α : Type} (heap : Nat → α) (source base old count k : Nat)
    (inside : k < count) :
    append heap source base old count (base+(old+k)) = heap (source+k) := by
  simpa only [append,Nat.add_assoc] using
    NHD_SnapshotWindows.byte heap source (base+old) count k inside

/-- Complete prefix++label view, proved symbolically rather than whole-buffer
native unwinding or assuming the desired String output. -/
theorem contents {α : Type} (heap : Nat → α) (source base old count : Nat) :
    view (append heap source base old count) base (old+count) =
      view heap base old ++ view heap source count := by
  unfold view
  rw [List.range_add,List.map_append,List.map_map]
  congr 1
  · apply List.map_congr_left
    intro k member
    exact prefix_frame heap source base old count k (List.mem_range.mp member)
  · apply List.map_congr_left
    intro k member
    exact appended_byte heap source base old count k (List.mem_range.mp member)

/-- The literal source remains immutable under the normal disjoint allocation
layout. This is an input-address separation condition, not an output equation. -/
theorem literal_frame {α : Type} (heap : Nat → α) (source base old count k : Nat)
    (separate : source+count ≤ base+old ∨ base+old+count ≤ source)
    (inside : k < count) :
    append heap source base old count (source+k) = heap (source+k) :=
  NHD_SnapshotWindows.source_preserved heap source (base+old) count k separate inside

#print axioms prefix_frame
#print axioms appended_byte
#print axioms contents
#print axioms literal_frame
end NHY_StringAppend
