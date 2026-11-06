import NJQ_Identity
import NJI_MasterModel
import NJI_V1Carrier
set_option autoImplicit false
namespace NJQ_Carrier
open Aeneas Aeneas.Std Result
abbrev I := NJI_Extracted.aspis_statement.pool_v1.format.PoolIdentityV1
abbrev CI := AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1
abbrev M := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev CM := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev C := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
abbrev CC := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
abbrev T := NJI_Extracted.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
abbrev CT := AdapterRw.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError
abbrev F := NJI_Extracted.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
abbrev CF := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1

def tree : T → CT
 | .TreeFull=>.TreeFull
 | .InsufficientCapacity=>.InsufficientCapacity
 | .IndexOutOfRange=>.IndexOutOfRange
 | .RootMismatch=>.RootMismatch
 | .NonCanonicalFrontier=>.NonCanonicalFrontier
 | .WrongLength=>.WrongLength
 | .WrongMagic=>.WrongMagic
 | .WrongVersion=>.WrongVersion
 | .WrongDepth=>.WrongDepth
 | .WrongTreeHash=>.WrongTreeHash
 | .WrongDigestEncoding=>.WrongDigestEncoding
 | .NonCanonicalDigest=>.NonCanonicalDigest
 | .NonZeroReserved=>.NonZeroReserved

def from_tree : CT → T
 | .TreeFull=>.TreeFull
 | .InsufficientCapacity=>.InsufficientCapacity
 | .IndexOutOfRange=>.IndexOutOfRange
 | .RootMismatch=>.RootMismatch
 | .NonCanonicalFrontier=>.NonCanonicalFrontier
 | .WrongLength=>.WrongLength
 | .WrongMagic=>.WrongMagic
 | .WrongVersion=>.WrongVersion
 | .WrongDepth=>.WrongDepth
 | .WrongTreeHash=>.WrongTreeHash
 | .WrongDigestEncoding=>.WrongDigestEncoding
 | .NonCanonicalDigest=>.NonCanonicalDigest
 | .NonZeroReserved=>.NonZeroReserved

theorem tree_roundtrip (v : T) : from_tree (tree v)=v := by
 cases v <;> simp only [tree,from_tree]

theorem tree_surjective (v : CT) : tree (from_tree v)=v := by
 cases v <;> simp only [tree,from_tree]

def error : F → CF
 | .WrongLength=>.WrongLength
 | .WrongMagic=>.WrongMagic
 | .WrongVersion=>.WrongVersion
 | .WrongLaneCount=>.WrongLaneCount
 | .WrongDigestEncoding=>.WrongDigestEncoding
 | .WrongDepth=>.WrongDepth
 | .WrongFormatBinding=>.WrongFormatBinding
 | .NonZeroReserved=>.NonZeroReserved
 | .ZeroRequiredBinding=>.ZeroRequiredBinding
 | .InvalidBoolean=>.InvalidBoolean
 | .InvalidMasterState=>.InvalidMasterState
 | .InvalidLane=>.InvalidLane
 | .LaneMasterMismatch=>.LaneMasterMismatch
 | .LaneOrderMismatch=>.LaneOrderMismatch
 | .LaneSequenceDecreased=>.LaneSequenceDecreased
 | .DuplicateCheckpoint=>.DuplicateCheckpoint
 | .CheckpointSequenceOverflow=>.CheckpointSequenceOverflow
 | .NonCanonicalDigest=>.NonCanonicalDigest
 | .Identity=>.Identity
 | .Policy=>.Policy
 | .Tree e=>.Tree (tree e)

def from_error : CF → F
 | .WrongLength=>.WrongLength
 | .WrongMagic=>.WrongMagic
 | .WrongVersion=>.WrongVersion
 | .WrongLaneCount=>.WrongLaneCount
 | .WrongDigestEncoding=>.WrongDigestEncoding
 | .WrongDepth=>.WrongDepth
 | .WrongFormatBinding=>.WrongFormatBinding
 | .NonZeroReserved=>.NonZeroReserved
 | .ZeroRequiredBinding=>.ZeroRequiredBinding
 | .InvalidBoolean=>.InvalidBoolean
 | .InvalidMasterState=>.InvalidMasterState
 | .InvalidLane=>.InvalidLane
 | .LaneMasterMismatch=>.LaneMasterMismatch
 | .LaneOrderMismatch=>.LaneOrderMismatch
 | .LaneSequenceDecreased=>.LaneSequenceDecreased
 | .DuplicateCheckpoint=>.DuplicateCheckpoint
 | .CheckpointSequenceOverflow=>.CheckpointSequenceOverflow
 | .NonCanonicalDigest=>.NonCanonicalDigest
 | .Identity=>.Identity
 | .Policy=>.Policy
 | .Tree e=>.Tree (from_tree e)

theorem error_roundtrip (v : F) : from_error (error v)=v := by
 cases v <;> simp only [error,from_error,tree_roundtrip,tree_surjective]

theorem error_surjective (v : CF) : error (from_error v)=v := by
 cases v <;> simp only [error,from_error,tree_roundtrip,tree_surjective]

def identity (v : I) : CI := ⟨v.pool,v.asset_mint,v.token_program,v.asset_id,v.deployment_domain⟩

def from_identity (v : CI) : I := ⟨v.pool,v.asset_mint,v.token_program,v.asset_id,v.deployment_domain⟩

theorem identity_roundtrip (v : I) : from_identity (identity v)=v := by
 cases v <;> simp only [identity,from_identity]

theorem identity_surjective (v : CI) : identity (from_identity v)=v := by
 cases v <;> simp only [identity,from_identity]

def checkpoint (v : C) : CC := ⟨v.bump,v.master,v.deployment_domain,v.checkpoint_sequence,v.global_root,v.lane_sequences⟩

def from_checkpoint (v : CC) : C := ⟨v.bump,v.master,v.deployment_domain,v.checkpoint_sequence,v.global_root,v.lane_sequences⟩

theorem checkpoint_roundtrip (v : C) : from_checkpoint (checkpoint v)=v := by
 cases v <;> simp only [checkpoint,from_checkpoint]

theorem checkpoint_surjective (v : CC) : checkpoint (from_checkpoint v)=v := by
 cases v <;> simp only [checkpoint,from_checkpoint]

def master (v : M) : CM := ⟨v.bump,identity v.identity,NJI_PolicyPort.policy v.verifier_policy,v.initialized_lane_mask,v.has_checkpoint,v.next_checkpoint_sequence,v.last_checkpoint_lane_sequences⟩

def from_master (v : CM) : M := ⟨v.bump,from_identity v.identity,NJI_PolicyPort.from_policy v.verifier_policy,v.initialized_lane_mask,v.has_checkpoint,v.next_checkpoint_sequence,v.last_checkpoint_lane_sequences⟩

theorem master_roundtrip (v : M) : from_master (master v)=v := by
 cases v <;> simp only [master,from_master,identity_roundtrip,identity_surjective,NJI_PolicyPort.policy_roundtrip,NJI_PolicyPort.policy_surjective]

theorem master_surjective (v : CM) : master (from_master v)=v := by
 cases v <;> simp only [master,from_master,identity_roundtrip,identity_surjective,NJI_PolicyPort.policy_roundtrip,NJI_PolicyPort.policy_surjective]

def identity_result (r : core.result.Result I NJI_PolicyPort.F) : core.result.Result CI NJI_PolicyPort.CF :=
 match r with | .Ok v=>.Ok (identity v) | .Err e=>.Err (NJI_PolicyPort.error e)
def from_identity_result (r : core.result.Result CI NJI_PolicyPort.CF) : core.result.Result I NJI_PolicyPort.F :=
 match r with | .Ok v=>.Ok (from_identity v) | .Err e=>.Err (NJI_PolicyPort.from_error e)
theorem identity_result_roundtrip (r : core.result.Result I NJI_PolicyPort.F) : from_identity_result (identity_result r)=r := by
 cases r <;> simp only [identity_result,from_identity_result,identity_roundtrip,NJI_PolicyPort.error_roundtrip]

def master_result (r : core.result.Result M F) : core.result.Result CM CF :=
 match r with | .Ok v=>.Ok (master v) | .Err e=>.Err (error e)
def from_master_result (r : core.result.Result CM CF) : core.result.Result M F :=
 match r with | .Ok v=>.Ok (from_master v) | .Err e=>.Err (from_error e)
theorem master_result_roundtrip (r : core.result.Result M F) : from_master_result (master_result r)=r := by
 cases r <;> simp only [master_result,from_master_result,master_roundtrip,error_roundtrip]

def checkpoint_result (r : core.result.Result C F) : core.result.Result CC CF :=
 match r with | .Ok v=>.Ok (checkpoint v) | .Err e=>.Err (error e)
def from_checkpoint_result (r : core.result.Result CC CF) : core.result.Result C F :=
 match r with | .Ok v=>.Ok (from_checkpoint v) | .Err e=>.Err (from_error e)
theorem checkpoint_result_roundtrip (r : core.result.Result C F) : from_checkpoint_result (checkpoint_result r)=r := by
 cases r <;> simp only [checkpoint_result,from_checkpoint_result,checkpoint_roundtrip,error_roundtrip]
#print axioms tree_roundtrip
#print axioms tree_surjective
#print axioms error_roundtrip
#print axioms error_surjective
#print axioms identity_roundtrip
#print axioms identity_surjective
#print axioms checkpoint_roundtrip
#print axioms checkpoint_surjective
#print axioms master_roundtrip
#print axioms master_surjective
#print axioms identity_result_roundtrip
#print axioms master_result_roundtrip
#print axioms checkpoint_result_roundtrip
end NJQ_Carrier
