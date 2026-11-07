import NMB_SnapshotReplay
import NMB_SnapshotPrefix
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotReplayAbort
open Aeneas Aeneas.Std Result AspisR1 NMB_Snapshot
/-- At an allocator abort, the entered token remains live and the owned prefix
is unchanged. The source stop contains no implicit guard-release suffix. -/
theorem source (s : State) (a : Nat) (allocation : Result Unit) :
 NMB_SnapshotReplay.replay s (NMB_SnapshotPrefix.allocationEvents s a allocation)=
 NMB_Snapshot.live s a := rfl
#print source
#print axioms source
end NMB_SnapshotReplayAbort
