import NMB_SnapshotAcquire
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotReturn
open Aeneas Aeneas.Std Result AspisR1 NLF_RefCell NLF_SdkModel NMB_Snapshot
/-- Normal-return bracket for arbitrary per-occurrence descriptors. Allocation
success is a branch of the intermediate fold, not a root precondition. -/
theorem result (x : NMB_Input.Input) (t a lo hi : Nat) (owned : List Owned) :
 (G (ready x t owned) a lo hi (.ok ())).result =
 .ok (x.snapshot a lo hi,returned (ready x t owned) a lo hi) := by
 unfold G
 rw [NMB_SnapshotAcquire.acquire]
 simp only [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_pure,
   NJU_Log.erase_if,bind_tc_ok]
 rw [NMB_SnapshotAcquire.release]
 split <;> simp [NJU_Log.erase_bind,NJU_Log.erase_record,NJU_Log.erase_pure,
  NJU_Log.erase_liftM,NJU_Log.erase_if,bind_tc_ok,returned,ready]
#print result
#print axioms result
end NMB_SnapshotReturn
