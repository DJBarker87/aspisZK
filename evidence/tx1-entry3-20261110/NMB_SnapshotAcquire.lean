import NMB_Snapshot
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotAcquire
open Aeneas Aeneas.Std Result AspisR1 NLF_RefCell NLF_SdkModel NMB_Snapshot
/-- No metadata/cell-equality premise: the original account occurrence selects
its admitted handle, even when another occurrence aliases that handle. -/
theorem acquire (x : NMB_Input.Input) (t a : Nat) (owned : List Owned) :
 try_borrow_data (ready x t owned).sdk a (ready x t owned).next =
 (acquired (ready x t owned) a,.ok (guard (ready x t owned) a)) := by
 apply shared_result <;> simp [ready,NMB_Input.Input.sdk]
theorem payload (x : NMB_Input.Input) (t a : Nat) (owned : List Owned) :
 (deref (acquired (ready x t owned) a) (guard (ready x t owned) a)).bytes =
 S2W_ReturnedCheckpoint.nativeBytes (x.buffers (x.handles a).1) := by
 rw [show deref (acquired (ready x t owned) a) (guard (ready x t owned) a)=
  ((ready x t owned).sdk.cells ((ready x t owned).sdk.accounts a).data).payload
  from shared_deref _ _ _]
 rfl
theorem release (x : NMB_Input.Input) (t a : Nat) (owned : List Owned) :
 NLF_SdkModel.release (acquired (ready x t owned) a) (guard (ready x t owned) a)=
 .ok (ready x t owned).sdk := by
 apply shared_release
 rfl
#print acquire
#print payload
#print release
#print axioms acquire
#print axioms payload
#print axioms release
end NMB_SnapshotAcquire
