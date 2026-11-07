import PCM_Semantics
import PCM_Spec_POOL_320
set_option autoImplicit false
namespace PCM
open RSL
abbrev Afterstate := PCM_POOL_320.Afterstate
structure TransferPublic where
  pool : B32
  deployment_domain : B32
  anchor_sequence : UInt64
  anchor_root : Digest
  nullifier : Digest
  asset_id : UInt32
  recipient_commitment : Digest
  change_commitment : Digest
structure WithdrawalPublic where
  pool : B32
  deployment_domain : B32
  anchor_sequence : UInt64
  anchor_root : Digest
  nullifier : Digest
  asset_id : UInt32
  amount : UInt32
  destination_token_account : B32
  change_commitment : Digest
inductive Payment where
  | transfer (pub : TransferPublic)
  | withdrawal (pub : WithdrawalPublic)
structure Request where
  verifier_profile : B32
  verifier_release : B32
  pool_program : B32
  pub : Payment
structure TerminalResult where
  transition_kind : UInt8
  master_account : B32
  selected_lane_account : B32
  output_lane : UInt8
  nullifier : Digest
  verified_afterstate : Afterstate
structure AuthenticatedResult where
  value : TerminalResult
  exact_bytes : Bytes
structure Common where
  master_account : B32
  checkpoint_account : B32
  selected_lane_account : B32
  output_lane : UInt8
  checkpoint_sequence : UInt64
  historical_global_anchor : Digest
  live_snapshot : LiveSnapshot
  candidate_afterstate : Afterstate
inductive Statement where
  | transfer (common : Common) (pub : TransferPublic)
  | withdrawal (common : Common) (pub : WithdrawalPublic)
structure DepositRequest where
  owner_key : Digest
  amount : UInt32
  salt : Digest
  encrypted_note_payload : Bytes
structure Rent where
  lamports_per_byte_year : UInt64
  exemption_threshold_bits : UInt64
  burn_percent : UInt8
structure PairWitness where
  first_commitment : Digest
  second_occupied : UInt32
  second_commitment : Digest
  second_occupancy_inverse : UInt32
structure Location where
  page_number : UInt64
  slot : UInt16
structure Header where
  pool : B32
  page_number : UInt64
  first_sequence : UInt64
  filled : UInt16
structure Append where
  leaf_index : UInt64
  root_sequence : UInt64
  root : Digest
  history : Location
inductive Preparation where
  | createOrAllocateSystemOwned
  | programOwnedZeroed
  deriving DecidableEq
inductive DepositMode where
  | genesis (preparation : Preparation) (bump : UInt8)
  | same (header : Header)
  | rollover (preparation : Preparation) (page_number : UInt64) (bump : UInt8)
structure TransferPlan where
  instruction : Instruction
  source : B32
  mint : B32
  vault : B32
  authority : B32
  amount : UInt64
  source_before : UInt64
  source_after : UInt64
  vault_before : UInt64
  vault_after : UInt64
  decimals : UInt8
structure WithdrawalPlan where
  instruction : Instruction
  mint : B32
  vault : B32
  destination : B32
  authority : B32
  amount : UInt64
  vault_before : UInt64
  vault_after : UInt64
  destination_before : UInt64
  destination_after : UInt64
  decimals : UInt8
  authority_bump : UInt8
structure Hints where
  current_page : UInt8
  next_page : UInt8
  vault_authority : UInt8
  vault_token_account : UInt8
inductive SpendPage where
  | genesis
  | same (header : Header)
  | rollover (next_index : Nat) (page_number : UInt64)
structure SpendLayout where
  page : SpendPage
  marker_index : Nat
  payer_index : Nat
  system_program_index : Nat
  registry_start : Nat
  verifier_index : Nat
  proof_index : Nat
  verifier_checkpoint_index : Option Nat
  token_start : Nat
structure DispatchPlan where
  selected_verifier : B32
  request_bytes : Bytes
structure PlannedCheckpoint where
  master : B32
  checkpoint : B32
  lane_sequences : List UInt64
  checkpoint_image : Bytes
  next_master_image : Bytes
structure Marker where
  transition_kind : UInt8
  pool : B32
  deployment_domain : B32
  nullifier : Digest
  retained_anchor_sequence : UInt64
  retained_anchor_root : Digest
  verifier_profile : B32
  verifier_release : B32
structure PlannedMarker where
  preparation : Preparation
  seed : B32
  encoded_marker : Bytes
abbrev ReadyMarker := PlannedMarker

/-- Exact field projections; no verifier root or Root0 premise is hidden here. -/
def Payment.nullifier : Payment → Digest
  | .transfer p => p.nullifier | .withdrawal p => p.nullifier
def Payment.transitionKind : Payment → UInt8
  | .transfer _ => 1 | .withdrawal _ => 2

def State.bytes (s : State) (a : AccountInfo) : Bytes := (s.sdk.cells a.cell).payload

def accountAt (accounts : List AccountInfo) (index : Nat) : Computation AccountInfo :=
  Computation.ofExcept (match accounts[index]? with
    | some a => .ok a | none => .error .notEnoughAccountKeys)
/-- A checked Rust index panics rather than returning NotEnoughAccountKeys. -/
def index (accounts : List AccountInfo) (i : Nat) : Computation AccountInfo :=
  match accounts[i]? with
  | some a => Computation.pure a
  | none => fun _ _ o => o = ⟨.abort, []⟩

def fullPure {A B : Type} (f : A → Except ProgramError B) : A → Computation B :=
  fun a => Computation.ofExcept (f a)

/-- All RSL interface fields are retained literally, rather than shadowed by
new carrier choices. PCM view/adaptation obligations will map into this type. -/
def PAGE_BYTES : Nat := 64 + 32 * 256
def HISTORY_CAPACITY : UInt16 := 256
def PAGE_SEED : Bytes := "aspis-pool-root-page-v1".toUTF8.toList
def SYSTEM_PROGRAM : B32 := zero32
abbrev SharedPoolLib := RSL.PoolLib

theorem shared_type : SharedPoolLib = RSL.PoolLib := rfl
#print axioms shared_type
end PCM
