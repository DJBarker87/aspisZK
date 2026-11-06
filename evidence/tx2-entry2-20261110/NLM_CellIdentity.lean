import NLM_SnapshotAcquire
set_option autoImplicit false
noncomputable section
namespace NLM_CellIdentity
open AspisR1.S2W_D189Entry NLM_Snapshot
/-- These are the cell identities projected by RuntimeEntrypointAdmission,
not addresses inferred from coincident payloads. -/
theorem data (e : Entry) (a t : Nat) (owned : List NLM_Snapshot.Owned) :
 (guard (ready e t owned) a).cell=(e.handles a).1 := rfl

theorem lamports (e : Entry) (a t : Nat) (owned : List NLM_Snapshot.Owned) :
 ((ready e t owned).sdk.accounts a).lamports=(e.handles a).2 := rfl

theorem shared_cell (e : Entry) (a b t : Nat) (owned : List NLM_Snapshot.Owned)
 (same : (e.handles a).1=(e.handles b).1) :
 (guard (ready e t owned) a).cell=(guard (ready e t owned) b).cell := same
#print data
#print lamports
#print shared_cell
#print axioms data
#print axioms lamports
#print axioms shared_cell
end NLM_CellIdentity
