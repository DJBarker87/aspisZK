import NMX_OwnedPackets
import RSL_TX2_233
set_option autoImplicit false
namespace NMX_Carrier
open Aeneas Aeneas.Std AdapterRw
/-- Exact-width scalar and list carriers; no field canonicality is assumed. -/
def byte (x : U8) : UInt8 := UInt8.ofNat x.val
def word (x : U32) : UInt32 := UInt32.ofNat x.val
def long (x : U64) : UInt64 := UInt64.ofNat x.val
def bytes (x : Slice U8) : RSL.Bytes := x.val.map byte
def key (x : Array U8 32#usize) : RSL.B32 :=
 ⟨x.val.map byte,by simpa using x.property⟩
def digest (x : Array U32 8#usize) : RSL.Digest := x.val.map word

def error : solana_program_error.ProgramError → RSL.ProgramError
 | .Custom n => .custom (word n)
 | .InvalidArgument => .invalidArgument
 | .InvalidInstructionData => .invalidInstructionData
 | .InvalidAccountData => .invalidAccountData
 | .AccountDataTooSmall => .accountDataTooSmall
 | .InsufficientFunds => .insufficientFunds
 | .IncorrectProgramId => .incorrectProgramId
 | .MissingRequiredSignature => .missingRequiredSignature
 | .AccountAlreadyInitialized => .accountAlreadyInitialized
 | .UninitializedAccount => .uninitializedAccount
 | .NotEnoughAccountKeys => .notEnoughAccountKeys
 | .AccountBorrowFailed => .accountBorrowFailed
 | .MaxSeedLengthExceeded => .maxSeedLengthExceeded
 | .InvalidSeeds => .invalidSeeds
 | .BorshIoError msg => .borshIoError msg
 | .AccountNotRentExempt => .accountNotRentExempt
 | .UnsupportedSysvar => .unsupportedSysvar
 | .IllegalOwner => .illegalOwner
 | .MaxAccountsDataAllocationsExceeded => .maxAccountsDataAllocationsExceeded
 | .InvalidRealloc => .invalidRealloc
 | .MaxInstructionTraceLengthExceeded => .maxInstructionTraceLengthExceeded
 | .BuiltinProgramsMustConsumeComputeUnits => .builtinProgramsMustConsumeComputeUnits
 | .InvalidAccountOwner => .invalidAccountOwner
 | .ArithmeticOverflow => .arithmeticOverflow
 | .Immutable => .immutable
 | .IncorrectAuthority => .incorrectAuthority

def reply {A B : Type} (f : A → B) : core.result.Result A solana_program_error.ProgramError → Except RSL.ProgramError B
 | .Ok a => .ok (f a)
 | .Err e => .error (error e)

def account (a : r1_pool_adapter.owned.OwnedAccount) : RSL.OwnedAccount :=
 ⟨key a.key,key a.owner,a.is_signer,a.is_writable,a.executable,
  reply (fun n => n.val) a.length,reply (fun b => b.val.map byte) a.bytes⟩

def identity (v : aspis_statement.pool_v1.format.PoolIdentityV1) : RSL.PoolIdentity :=
 ⟨key v.pool,key v.asset_mint,key v.token_program,word v.asset_id,key v.deployment_domain⟩
def policy (v : aspis_statement.pool_v1.format.VerifierPolicyV1) : RSL.VerifierPolicy :=
 ⟨byte v.flags,key v.registry_program,key v.registry_authority,key v.policy_binding⟩
def master (v : NMX_OwnedPackets.Master) : RSL.Master :=
 ⟨byte v.bump,identity v.identity,policy v.verifier_policy,byte v.initialized_lane_mask,
  v.has_checkpoint,long v.next_checkpoint_sequence,v.last_checkpoint_lane_sequences.val.map long⟩
def checkpoint (v : NMX_OwnedPackets.Checkpoint) : RSL.Checkpoint :=
 ⟨byte v.bump,key v.master,key v.deployment_domain,long v.checkpoint_sequence,
  digest v.global_root,v.lane_sequences.val.map long⟩
def tree (v : aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) : RSL.Tree :=
 ⟨long v.next_leaf_index,digest v.root,v.frontier.val.map digest⟩
def lane (v : NMX_OwnedPackets.Lane) : RSL.LaneState :=
 ⟨byte v.bump,key v.master,byte v.lane_id,tree v.tree⟩
def snapshot (v : NMX_OwnedPackets.Snapshot) : RSL.LiveSnapshot :=
 ⟨key v.pool,key v.deployment_domain,long v.sequence,long v.next_pair_index,
  digest v.current_root,v.frontier.val.map digest⟩
def auth (v : NMX_OwnedPackets.Auth) : RSL.Authenticated :=
 ⟨key v.masterAccount,key v.checkpointAccount,key v.selectedLaneAccount,
  master v.master.payload,checkpoint v.checkpoint.payload,lane v.selectedLane.payload,
  snapshot v.liveSnapshot.payload⟩

/-- Payload conversion keeps every byte/limb; nominal owners stay in the
input packet and are not identified with physical pointers by this map. -/
theorem four_payloads (v : NMX_OwnedPackets.Auth) :
 (auth v).master = master v.master.payload ∧
 (auth v).checkpoint = checkpoint v.checkpoint.payload ∧
 (auth v).selected_lane = lane v.selectedLane.payload ∧
 (auth v).live_snapshot = snapshot v.liveSnapshot.payload := ⟨rfl,rfl,rfl,rfl⟩
#print axioms four_payloads
end NMX_Carrier
