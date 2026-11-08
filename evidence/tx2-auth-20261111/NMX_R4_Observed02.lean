import NMX_R4_CallContext
import NMX_R4_PdaObservation
import NMX_R4_CallScript02
import NMX_Fold02
import NMX_R4_Observed03
set_option autoImplicit false
noncomputable section
namespace NMX_R4_Observed02
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallRun NMX_R4_CallContext

theorem e030 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 observe c (NMX_R4_CallScript02.t030 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p030 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint) := by
 unfold NMX_R4_CallScript02.t030 NMX_Fold02.p030
 apply NMX_R4_ObservedStep.scalar
 intro checkpointMasterBytes
 exact NMX_R4_Observed03.e031 c pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes
#print axioms e030

theorem e029 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) :
 observe c (NMX_R4_CallScript02.t029 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p029 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes) := by
 unfold NMX_R4_CallScript02.t029 NMX_Fold02.p029
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.checkpoint checkpointBytes)) (fun reply => NMX_R4_TryObservation.after reply (fun checkpoint => NMX_R4_CallScript02.t030 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpoint))) = _
 apply NMX_R4_ObservedStep.child
 intro checkpoint
 exact NMX_R4_Observed02.e030 c pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e029

theorem e028 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript02.t028 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p028 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey) := by
 unfold NMX_R4_CallScript02.t028 NMX_Fold02.p028
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.data checkpointAccount)) (fun reply => NMX_R4_TryObservation.after reply (fun checkpointBytes => NMX_R4_CallScript02.t029 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes))) = _
 apply NMX_R4_ObservedStep.child
 intro checkpointBytes
 exact NMX_R4_Observed02.e029 c pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes
#print axioms e028

theorem e027 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript02.t027 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p027 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) := by
 unfold NMX_R4_CallScript02.t027 NMX_Fold02.p027
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.registry verifier pool masterAccount master.payload registryAccount entryAccount slot)) (fun reply => NMX_R4_TryObservation.after reply (fun _unit => NMX_R4_CallScript02.t028 c.owners (ops c) pool outputLane checkpointAccount laneAccount master masterKey))) = _
 apply NMX_R4_ObservedStep.child
 intro _unit
 exact NMX_R4_Observed02.e028 c pool outputLane checkpointAccount laneAccount master masterKey
#print axioms e027

theorem e026 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) :
 observe c (NMX_R4_CallScript02.t026 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p026 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda) := by
 unfold NMX_R4_CallScript02.t026 NMX_Fold02.p026
 cases condition : (wrongMasterPda) with
 | true => rfl
 | false => exact NMX_R4_Observed02.e027 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e026

theorem e025 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript02.t025 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p025 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster) := by
 unfold NMX_R4_CallScript02.t025 NMX_Fold02.p025
 apply NMX_R4_ObservedStep.scalar
 intro wrongMasterPda
 exact NMX_R4_Observed02.e026 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda
#print axioms e025

theorem e024 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) :
 observe c (NMX_R4_CallScript02.t024 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p024 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds) := by
 unfold NMX_R4_CallScript02.t024 NMX_Fold02.p024
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.pda masterSeeds pool) (fun reply => NMX_R4_PdaObservation.after r1_pool_adapter.owned.authenticate_asq8_accounts.closure.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError reply (fun derivedMaster => NMX_R4_CallScript02.t025 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster))) = _
 apply NMX_R4_PdaObservation.step
 · rfl
 intro derivedMaster
 exact NMX_R4_Observed02.e025 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster
#print axioms e024

theorem e023 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript02.t023 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p023 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey) := by
 unfold NMX_R4_CallScript02.t023 NMX_Fold02.p023
 apply NMX_R4_ObservedStep.scalar
 intro mintSeed
 simp only [NMX_R4_CallLaws.observed_scalar,NMX_R3_RegistryRun.scalar,NMX_R2_Observation.bind]
 let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
 let masterSeeds := Array.to_slice (Array.make 3#usize [
   r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
 exact NMX_R4_Observed02.e024 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds
#print axioms e023

theorem e022 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript02.t022 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p022 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) := by
 unfold NMX_R4_CallScript02.t022 NMX_Fold02.p022
 apply NMX_R4_ObservedStep.scalar
 intro mintKey
 exact NMX_R4_Observed02.e023 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey
#print axioms e022

theorem e021 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) :
 observe c (NMX_R4_CallScript02.t021 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold02.p021 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes) := by
 unfold NMX_R4_CallScript02.t021 NMX_Fold02.p021
 cases condition : ((master.payload.initialized_lane_mask != allLanes)) with
 | true => rfl
 | false => exact NMX_R4_Observed02.e022 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e021
end NMX_R4_Observed02
end
