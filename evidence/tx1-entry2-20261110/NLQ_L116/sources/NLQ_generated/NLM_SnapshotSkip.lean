import NLM_SnapshotTrace
set_option autoImplicit false
noncomputable section
namespace NLM_Snapshot
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry NLF_SdkModel
/-- A rejected-length snapshot never calls the allocator. An arbitrary
allocator failure cannot be turned into a new caller success premise. -/
theorem skip_allocation (e : Entry) (t a lo hi : Nat) (owned : List Owned)
 (allocation : Result Unit)
 (skip : ¬ ((AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=lo ∨
            (AspisR1.S2W_ReturnedCheckpoint.nativeBytes (e.buffers (e.handles a).1)).length=hi)) :
 G (ready e t owned) a lo hi allocation=G (ready e t owned) a lo hi (.ok ()) := by
 unfold G
 rw [acquire]
 rw [←current_payload e t a owned] at skip
 simp only [acquired,guard,shared_deref] at skip
 simp [Bind.bind,Pure.pure,NJU_Log.bind,NJU_Log.record,skip,acquired,guard,shared_deref]
#print skip_allocation
#print axioms skip_allocation
end NLM_Snapshot
