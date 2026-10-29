import R1Z.PV_OWNC_GuardReturn
import R1Z.PV_OWNB_SnapshotFold
set_option autoImplicit false
namespace R1Z.PV_OWNC_SourceLoop
open PV_OWNB_Cursor PV_OWN_Link PV_OWNC_FoldSource
/-- Non-ZST source try_fold, specialized to the total path predicate and POD
sink. Iteration, not kernel normalization of the concrete 127-cell source. -/
def run (keep : Link → Bool) : Nat → Cursor → Cursor
 | 0,q => q
 | n+1,q => run keep n (sourceStep keep q)

theorem snapshot_binding (keep : Link → Bool) (n : Nat) (q : Cursor) :
 run keep n q=PV_OWNB_SnapshotFold.run keep n q := by
 induction n generalizing q with
 | zero => rfl
 | succ n ih =>
  rw [run,ih,step_binding,PV_OWNB_SnapshotFold.run]

theorem completed (keep : Link → Bool) (q : Cursor) (h:Valid q) :
 let result:=run keep (q.length-q.read) q
 Valid result ∧ result.read=q.length := by
 rw [snapshot_binding]
 have hv:=h
 unfold Valid at h
 refine ⟨PV_OWNB_SnapshotFold.valid keep _ q hv (by omega),?_⟩
 rw [PV_OWNB_SnapshotFold.advances]
 omega
attribute [local irreducible] run
#print axioms snapshot_binding
#print axioms completed
end R1Z.PV_OWNC_SourceLoop
