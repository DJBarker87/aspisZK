import NMB_Input
set_option autoImplicit false
noncomputable section
namespace NMB_InputSnapshot
open Aeneas Aeneas.Std Result AspisR1 NMB_Input
theorem metadata (x : Input) (a lo hi : Nat) :
 (x.snapshot a lo hi).key=(x.descriptors a).key ∧
 (x.snapshot a lo hi).owner=(x.descriptors a).owner ∧
 (x.snapshot a lo hi).is_signer=(x.descriptors a).is_signer ∧
 (x.snapshot a lo hi).is_writable=(x.descriptors a).is_writable ∧
 (x.snapshot a lo hi).executable=(x.descriptors a).executable := by
 exact ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem length (x : Input) (a lo hi : Nat) :
 (x.snapshot a lo hi).length=.Ok (Slice.len (x.buffers (x.handles a).1)) := rfl
theorem admitted (x : Input) (a lo hi : Nat)
 (extent : (x.buffers (x.handles a).1).val.length=lo ∨
   (x.buffers (x.handles a).1).val.length=hi) :
 (x.snapshot a lo hi).bytes=.Ok (x.buffers (x.handles a).1) := by
 simp [Input.snapshot,extent]
theorem malformed (x : Input) (a lo hi : Nat)
 (extent : ¬ ((x.buffers (x.handles a).1).val.length=lo ∨
   (x.buffers (x.handles a).1).val.length=hi)) :
 (x.snapshot a lo hi).bytes=.Err .InvalidAccountData := by
 simp [Input.snapshot,extent]
#print metadata
#print axioms metadata
#print axioms length
#print axioms admitted
#print axioms malformed
end NMB_InputSnapshot
