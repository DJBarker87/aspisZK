import NMB_SnapshotReplay
import NMB_SnapshotTrace
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotReplayNormal
open Aeneas Aeneas.Std Result AspisR1 NMB_Snapshot
theorem source (x : NMB_Input.Input) (t a lo hi : Nat) (owned : List Owned) :
 NMB_SnapshotReplay.replay (ready x t owned) (G (ready x t owned) a lo hi (.ok ())).events=
 returned (ready x t owned) a lo hi := by
 rw [NMB_SnapshotTrace.source]
 dsimp only [NMB_SnapshotTrace.events]
 split_ifs <;> rfl
#print source
#print axioms source
end NMB_SnapshotReplayNormal
