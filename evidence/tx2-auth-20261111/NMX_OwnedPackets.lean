import NMN_242Interface
set_option autoImplicit false
namespace NMX_OwnedPackets
open Aeneas Aeneas.Std AdapterRw
abbrev PE := solana_program_error.ProgramError
abbrev Master := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev Checkpoint := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
abbrev Lane := aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
abbrev Snapshot := aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Statement := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Candidate := aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
/-- Logical owner identity is retained beside the complete emitted payload.
This carrier does not assert an allocation or supply a native correspondence. -/
structure Box (α : Type) where
 owner : Nat
 payload : α
structure Auth where
 masterAccount : Array U8 32#usize
 checkpointAccount : Array U8 32#usize
 selectedLaneAccount : Array U8 32#usize
 master : Box Master
 checkpoint : Box Checkpoint
 selectedLane : Box Lane
 liveSnapshot : Box Snapshot
structure Scanned where
 candidate : Box Candidate
 proofLength : Usize
structure Validated where
 statement : Box Statement
 proofLength : Usize

def Auth.erase (a : Auth) : r1_pool_adapter.AuthenticatedAsq8Accounts :=
 ⟨a.masterAccount,a.checkpointAccount,a.selectedLaneAccount,
  a.master.payload,a.checkpoint.payload,a.selectedLane.payload,a.liveSnapshot.payload⟩
def Auth.owners (a : Auth) : List Nat :=
 [a.master.owner,a.checkpoint.owner,a.selectedLane.owner,a.liveSnapshot.owner]
def Auth.Fresh (a : Auth) (inputOwners : List Nat) : Prop :=
 a.owners.Nodup ∧ ∀ o ∈ a.owners, o ∉ inputOwners

def Scanned.erase (s : Scanned) : r1_pool_adapter.ScannedAsqaProof :=
 ⟨s.candidate.payload,s.proofLength⟩
def Validated.erase (v : Validated) : r1_pool_adapter.ValidatedAsqa :=
 ⟨v.statement.payload,v.proofLength⟩
/-- A stopped execution has only its chronological prefix and cause. There is
no returned owner, post-world, or hypothetical cleanup state on this arm. -/
inductive Stop where
 | failed (error : Aeneas.Std.Error)
 | diverged
inductive End (World Event Reply : Type) where
 | returned (reply : core.result.Result Reply PE) (post : World) (events : List Event)
 | stopped (events : List Event) (cause : Stop)

def End.events {W E A : Type} : End W E A → List E
 | .returned _ _ events => events
 | .stopped events _ => events

def End.value {W E A : Type} : End W E A → Result (core.result.Result A PE)
 | .returned reply _ _ => .ok reply
 | .stopped _ (.failed error) => .fail error
 | .stopped _ .diverged => .div

theorem auth_payloads (a : Auth) :
 a.erase.master = a.master.payload ∧
 a.erase.checkpoint = a.checkpoint.payload ∧
 a.erase.selected_lane = a.selectedLane.payload ∧
 a.erase.live_snapshot = a.liveSnapshot.payload := ⟨rfl,rfl,rfl,rfl⟩
theorem validated_payload (a : Validated) :
 a.erase.statement = a.statement.payload ∧ a.erase.proof_length = a.proofLength := ⟨rfl,rfl⟩
theorem stopped_events {W E A : Type} (events : List E) (cause : Stop) :
 (End.stopped events cause : End W E A).events = events := rfl
#print axioms auth_payloads
#print axioms validated_payload
#print axioms stopped_events
end NMX_OwnedPackets
