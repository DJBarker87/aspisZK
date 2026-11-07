import NMT_345TryCongr
import NMT_345Boundary01
import NMT_345BoundaryReadonlyProof
import NMT_345BoundaryReadonlyPublic
import NMT_345BoundaryCheckpoint
import NMT_345BoundaryCheckpointData
import NMT_345BoundaryZero
import NMT_345BoundaryPublicData
import NMT_345BoundaryDecode
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
/-- Typed source prefix, not a row root. All original context survives. -/
def prefixFold {W : Type} (c : Calls) (s : Selected W)
 (next : Decoded W → Result Ret) : Result Ret :=
 tryStep (c.c15 (selectedArray s)) fun _ =>
 tryStep (c.c13 s.proofAccount) fun _ =>
 tryStep (c.c13 s.publicAccount) fun _ =>
 tryStep (c.c14 s.checkpointAccount s.program true) fun _ =>
 tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.checkpointAccount) fun ck =>
 tryStep (c.c16 ck) fun _ =>
 tryStep (NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount.data c.c10 s.publicAccount) fun pub =>
 tryStep (c.c12 pub) fun statement => next ⟨⟨⟨s,ck⟩,pub⟩,statement⟩

theorem prefix_fold {W : Type} (c : Calls) (s : Selected W) :
 rawSelected c s = prefixFold c s (raw07 c) := by
 unfold prefixFold
 rw [boundary_distinct]
 apply try_congr
 intro _
 rw [boundaryReadonlyProof]
 apply try_congr
 intro _
 rw [boundaryReadonlyPublic]
 apply try_congr
 intro _
 rw [boundaryCheckpoint]
 apply try_congr
 intro _
 rw [boundaryCheckpointData]
 apply try_congr
 intro ck
 rw [boundaryZero]
 apply try_congr
 intro _
 rw [boundaryPublicData]
 apply try_congr
 intro pub
 rw [boundaryDecode]
#print axioms prefix_fold
end NMT_345
