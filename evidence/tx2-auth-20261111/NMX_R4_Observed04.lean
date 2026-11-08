import NMX_R4_FreeCongruence
import NMX_R4_CallContext
import NMX_R4_PdaObservation
import NMX_R4_CallScript04
import NMX_Fold04
import NMX_R4_Observed05
set_option autoImplicit false
noncomputable section
namespace NMX_R4_Observed04
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallRun NMX_R4_CallContext

theorem e050 (c : Context) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) :
 observe c (NMX_R4_CallScript04.t050 c.owners (ops c) master masterKey checkpoint checkpointKey lane laneKey wrongLanePda) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p050 c.owners (ops c) master masterKey checkpoint checkpointKey lane laneKey wrongLanePda) := by
 unfold NMX_R4_CallScript04.t050 NMX_Fold04.p050
 cases condition : (wrongLanePda) with
 | true => rfl
 | false => exact NMX_R4_Observed05.e051 c master masterKey checkpoint checkpointKey lane laneKey
#print axioms e050

theorem e049 (c : Context) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript04.t049 c.owners (ops c) master masterKey checkpoint checkpointKey lane derivedLane laneKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p049 c.owners (ops c) master masterKey checkpoint checkpointKey lane derivedLane laneKey) := by
 unfold NMX_R4_CallScript04.t049 NMX_Fold04.p049
 apply NMX_R4_ObservedStep.scalar
 intro wrongLanePda
 exact NMX_R4_Observed04.e050 c master masterKey checkpoint checkpointKey lane laneKey wrongLanePda
#print axioms e049

theorem e048 (c : Context) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript04.t048 c.owners (ops c) laneAccount master masterKey checkpoint checkpointKey lane derivedLane) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p048 c.owners (ops c) laneAccount master masterKey checkpoint checkpointKey lane derivedLane) := by
 unfold NMX_R4_CallScript04.t048 NMX_Fold04.p048
 apply NMX_R4_ObservedStep.scalar
 intro laneKey
 exact NMX_R4_Observed04.e049 c master masterKey checkpoint checkpointKey lane derivedLane laneKey
#print axioms e048

theorem e047 (c : Context) (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) :
 observe c (NMX_R4_CallScript04.t047 c.owners (ops c) pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p047 c.owners (ops c) pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds) := by
 unfold NMX_Fold04.p047
 have same : NMX_R4_CallScript04.t047 c.owners (ops c) pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds = NMX_R4_CallProgram.bind (NMX_R4_CallProgram.pda laneSeeds pool) (fun reply => NMX_R4_PdaObservation.after r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError reply (fun derivedLane => NMX_R4_CallScript04.t048 c.owners (ops c) laneAccount master masterKey checkpoint checkpointKey lane derivedLane)) := by
  unfold NMX_R4_CallScript04.t047 NMX_R4_PdaObservation.after NMX_R4_TryObservation.after
  apply NMX_R4_FreeCongruence.step
  intro reply
  apply NMX_R4_FreeCongruence.step
  intro response
  apply NMX_R4_FreeCongruence.step
  intro control
  cases control <;> rfl
 rw [same]
 have h := NMX_R4_PdaObservation.step c laneSeeds pool r1_pool_adapter.owned.authenticate_asq8_accounts.closure_2.Insts.CoreOpsFunctionFnOnceTuplePubkeyErrorProgramError (by rfl) (fun derivedLane => NMX_R4_CallScript04.t048 c.owners (ops c) laneAccount master masterKey checkpoint checkpointKey lane derivedLane) (fun derivedLane => NMX_Fold04.p048 c.owners (ops c) laneAccount master masterKey checkpoint checkpointKey lane derivedLane) (fun derivedLane => NMX_R4_Observed04.e048 c laneAccount master masterKey checkpoint checkpointKey lane derivedLane)
 exact h
#print axioms e047

theorem e046 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 observe c (NMX_R4_CallScript04.t046 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p046 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) := by
 unfold NMX_R4_CallScript04.t046 NMX_Fold04.p046
 apply NMX_R4_ObservedStep.scalar
 intro laneMasterSeed
 simp only [NMX_R4_CallLaws.observed_scalar,NMX_R3_RegistryRun.scalar,NMX_R2_Observation.bind]
 let laneIdSeed := Array.to_slice (Array.make 1#usize [outputLane])
 let laneBump := Array.to_slice (Array.make 1#usize [lane.payload.bump])
 let laneSeeds := Array.to_slice (Array.make 4#usize [
   r1_pool_adapter.PAIR_FOREST_LANE_SEED,laneMasterSeed,laneIdSeed,laneBump])
 exact NMX_R4_Observed04.e047 c pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds
#print axioms e046

theorem e045 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 observe c (NMX_R4_CallScript04.t045 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p045 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) := by
 unfold NMX_R4_CallScript04.t045 NMX_Fold04.p045
 cases condition : ((lane.payload.lane_id != outputLane)) with
 | true => rfl
 | false => exact NMX_R4_Observed04.e046 c pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e045

theorem e044 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) :
 observe c (NMX_R4_CallScript04.t044 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p044 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster) := by
 unfold NMX_R4_CallScript04.t044 NMX_Fold04.p044
 cases condition : (wrongLaneMaster) with
 | true => rfl
 | false => exact NMX_R4_Observed04.e045 c pool outputLane laneAccount master masterKey checkpoint checkpointKey lane
#print axioms e044

theorem e043 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) :
 observe c (NMX_R4_CallScript04.t043 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p043 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes) := by
 unfold NMX_R4_CallScript04.t043 NMX_Fold04.p043
 apply NMX_R4_ObservedStep.scalar
 intro wrongLaneMaster
 exact NMX_R4_Observed04.e044 c pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster
#print axioms e043

theorem e042 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 observe c (NMX_R4_CallScript04.t042 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p042 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) := by
 unfold NMX_R4_CallScript04.t042 NMX_Fold04.p042
 apply NMX_R4_ObservedStep.scalar
 intro laneMasterBytes
 exact NMX_R4_Observed04.e043 c pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes
#print axioms e042

theorem e041 (c : Context) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) :
 observe c (NMX_R4_CallScript04.t041 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold04.p041 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes) := by
 unfold NMX_Fold04.p041
 have same : NMX_R4_CallScript04.t041 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes = NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.lane laneBytes)) (fun reply => NMX_R4_TryObservation.after reply (fun lane => NMX_R4_CallScript04.t042 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)) := by
  unfold NMX_R4_CallScript04.t041 NMX_R4_TryObservation.after
  apply NMX_R4_FreeCongruence.step
  intro reply
  apply NMX_R4_FreeCongruence.step
  intro response
  cases response <;> rfl
 rw [same]
 have h := NMX_R4_ObservedStep.child c (.lane laneBytes) (fun lane => NMX_R4_CallScript04.t042 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) (fun lane => NMX_Fold04.p042 c.owners (ops c) pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) (fun lane => NMX_R4_Observed04.e042 c pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)
 exact h
#print axioms e041
end NMX_R4_Observed04
end
