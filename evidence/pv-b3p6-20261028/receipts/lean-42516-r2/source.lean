import PV_B3P_ProjectV3Law226
namespace PV_B3P_ZeroSource226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

def z : U32 := aspis_core.field.M31.ZERO
def digest : Array U32 8#usize := Array.repeat 8#usize z
def frontier : Array (Array U32 8#usize) 20#usize := Array.repeat 20#usize digest
def metadata : Array U8 32#usize := Array.repeat 32#usize 0#u8

def owned (b : Bool) : reference226.OwnedPublic :=
  ⟨b,digest,digest,z,digest,digest,z,0#u64,frontier,digest,frontier⟩

def transition : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  { live_snapshot := ⟨metadata,metadata,0#u64,0#u64,digest,frontier⟩
    candidate_afterstate := ⟨0#u64,digest,frontier⟩ }

def source (b : Bool) : reference226.Source :=
  if b then .Withdrawal
    ⟨metadata,metadata,0#u64,digest,digest,z,z,metadata,digest⟩ transition
  else .Transfer ⟨metadata,metadata,0#u64,digest,digest,z,digest,digest⟩ transition

theorem projection (b : Bool) : reference226.project (source b) = .ok (owned b) := by
  cases b <;> rfl

theorem canonical_digest : ∀ m ∈ digest.val, m < 2147483647#u32 := by
  intro m hm
  have he : m = z := (List.mem_replicate.mp hm).2
  rw [he]
  change (0#u32) < 2147483647#u32
  decide

theorem canonical_frontier : ∀ row ∈ frontier.val,
    ∀ m ∈ row.val, m < 2147483647#u32 := by
  intro row hr
  have he : row = digest := (List.mem_replicate.mp hr).2
  rw [he]
  exact canonical_digest

#print axioms projection
#print axioms canonical_digest
#print axioms canonical_frontier
end PV_B3P_ZeroSource226V3
