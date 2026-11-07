import NMX_BindCongruence
import NMX_PdaMap
import NMX_Actual02
import NMX_Fold02
import NMX_Match03
set_option autoImplicit false
noncomputable section
namespace NMX_Match02
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

/-- Actual emitted occurrence 30; complete arbitrary reply/control arms. -/
theorem e030 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_Fold02.v030 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint =
 NMX_Actual02.t030 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpoint.payload := by
 unfold NMX_Fold02.v030 NMX_Actual02.t030
 apply NMX_BindCongruence.step
 intro checkpointMasterBytes
 exact NMX_Match03.e031 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes
#print axioms e030

/-- Actual emitted occurrence 29; complete arbitrary reply/control arms. -/
theorem e029 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) :
 NMX_Fold02.v029 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes =
 NMX_Actual02.t029 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey checkpointBytes := by
 unfold NMX_Fold02.v029 NMX_Actual02.t029
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok value =>
   let checkpoint : Box Checkpoint := ⟨owners.checkpoint,value⟩
   exact NMX_Match02.e030 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint
#print axioms e029

/-- Actual emitted occurrence 28; complete arbitrary reply/control arms. -/
theorem e028 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Fold02.v028 owners ops pool outputLane checkpointAccount laneAccount master masterKey =
 NMX_Actual02.t028 owners ops pool outputLane checkpointAccount laneAccount master.payload masterKey := by
 unfold NMX_Fold02.v028 NMX_Actual02.t028
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok checkpointBytes =>
   exact NMX_Match02.e029 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes
#print axioms e028

/-- Actual emitted occurrence 27; complete arbitrary reply/control arms. -/
theorem e027 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Fold02.v027 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey =
 NMX_Actual02.t027 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey := by
 unfold NMX_Fold02.v027 NMX_Actual02.t027
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok unit =>
   exact NMX_Match02.e028 owners ops pool outputLane checkpointAccount laneAccount master masterKey
#print axioms e027

/-- Actual emitted occurrence 26; complete arbitrary reply/control arms. -/
theorem e026 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) :
 NMX_Fold02.v026 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda =
 NMX_Actual02.t026 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey wrongMasterPda := by
 unfold NMX_Fold02.v026 NMX_Actual02.t026
 by_cases condition : (wrongMasterPda) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match02.e027 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e026

/-- Actual emitted occurrence 25; complete arbitrary reply/control arms. -/
theorem e025 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) :
 NMX_Fold02.v025 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster =
 NMX_Actual02.t025 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey derivedMaster := by
 unfold NMX_Fold02.v025 NMX_Actual02.t025
 apply NMX_BindCongruence.step
 intro wrongMasterPda
 exact NMX_Match02.e026 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda
#print axioms e025

/-- Actual emitted occurrence 24; complete arbitrary reply/control arms. -/
theorem e024 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) :
 NMX_Fold02.v024 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds =
 NMX_Actual02.t024 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey masterSeeds := by
 unfold NMX_Fold02.v024 NMX_Actual02.t024
 rw [NMX_PdaMap.try_bind]
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok derivedMaster =>
   exact NMX_Match02.e025 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster
#print axioms e024

/-- Actual emitted occurrence 23; complete arbitrary reply/control arms. -/
theorem e023 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) :
 NMX_Fold02.v023 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey =
 NMX_Actual02.t023 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey mintKey := by
 unfold NMX_Fold02.v023 NMX_Actual02.t023
 apply NMX_BindCongruence.step
 intro mintSeed
 let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
 let masterSeeds := Array.to_slice (Array.make 3#usize [
   r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
 exact NMX_Match02.e024 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds
#print axioms e023

/-- Actual emitted occurrence 22; complete arbitrary reply/control arms. -/
theorem e022 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Fold02.v022 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey =
 NMX_Actual02.t022 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey := by
 unfold NMX_Fold02.v022 NMX_Actual02.t022
 apply NMX_BindCongruence.step
 intro mintKey
 exact NMX_Match02.e023 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey
#print axioms e022

/-- Actual emitted occurrence 21; complete arbitrary reply/control arms. -/
theorem e021 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) :
 NMX_Fold02.v021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes =
 NMX_Actual02.t021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey allLanes := by
 unfold NMX_Fold02.v021 NMX_Actual02.t021
 by_cases condition : ((master.payload.initialized_lane_mask != allLanes)) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match02.e022 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e021
end NMX_Match02
end
