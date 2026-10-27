import RPz7_S6NativeSnapshotReadDigestV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotReadArray
open AspisR1TerminalDecoder

def read_array (N : Usize) (bytes : Slice U8) : Result (Array U8 N) := do
  let converted ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 bytes
  atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy N core.marker.CopyU8) converted

@[step] theorem read_array_spec (N : Usize) (bytes : Slice U8) (size : bytes.length=N.val) :
    read_array N bytes ⦃ result => result.val=bytes.val ⦄ := by
  unfold read_array
  step*
  all_goals (cases converted <;> simp_all)
  all_goals step*
  all_goals simp_all

#print axioms read_array_spec
end AspisS6NativeSnapshotReadArray
