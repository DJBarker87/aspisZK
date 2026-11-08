import NMX_R4_CallContext
import NMX_R4_PdaObservation
import NMX_R4_CallScript01
import NMX_Fold01
import NMX_R4_Observed02
set_option autoImplicit false
noncomputable section
namespace NMX_R4_Observed01
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallRun NMX_R4_CallContext

theorem e020 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript01.t020 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p020 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) := by
 unfold NMX_R4_CallScript01.t020 NMX_Fold01.p020
 apply NMX_R4_ObservedStep.scalar
 intro allLanes
 exact NMX_R4_Observed02.e021 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes
#print axioms e020

theorem e019 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) :
 observe c (NMX_R4_CallScript01.t019 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p019 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster) := by
 unfold NMX_R4_CallScript01.t019 NMX_Fold01.p019
 cases condition : (wrongMaster) with
 | true => rfl
 | false => exact NMX_R4_Observed01.e020 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e019

theorem e018 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) :
 observe c (NMX_R4_CallScript01.t018 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p018 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes) := by
 unfold NMX_R4_CallScript01.t018 NMX_Fold01.p018
 apply NMX_R4_ObservedStep.scalar
 intro wrongMaster
 exact NMX_R4_Observed01.e019 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster
#print axioms e018

theorem e017 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 observe c (NMX_R4_CallScript01.t017 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p017 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) := by
 unfold NMX_R4_CallScript01.t017 NMX_Fold01.p017
 apply NMX_R4_ObservedStep.scalar
 intro masterKeyBytes
 exact NMX_R4_Observed01.e018 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes
#print axioms e017

theorem e016 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) :
 observe c (NMX_R4_CallScript01.t016 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p016 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master) := by
 unfold NMX_R4_CallScript01.t016 NMX_Fold01.p016
 apply NMX_R4_ObservedStep.scalar
 intro masterKey
 exact NMX_R4_Observed01.e017 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e016

theorem e015 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) :
 observe c (NMX_R4_CallScript01.t015 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p015 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes) := by
 unfold NMX_R4_CallScript01.t015 NMX_Fold01.p015
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.master masterBytes)) (fun reply => NMX_R4_TryObservation.after reply (fun master => NMX_R4_CallScript01.t016 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master))) = _
 apply NMX_R4_ObservedStep.child
 intro master
 exact NMX_R4_Observed01.e016 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master
#print axioms e015

theorem e014 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript01.t014 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p014 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount) := by
 unfold NMX_R4_CallScript01.t014 NMX_Fold01.p014
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.data masterAccount)) (fun reply => NMX_R4_TryObservation.after reply (fun masterBytes => NMX_R4_CallScript01.t015 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes))) = _
 apply NMX_R4_ObservedStep.child
 intro masterBytes
 exact NMX_R4_Observed01.e015 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes
#print axioms e014

theorem e013 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript01.t013 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p013 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) := by
 unfold NMX_R4_CallScript01.t013 NMX_Fold01.p013
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.distinct (Array.make 7#usize [proof,masterAccount,checkpointAccount,
  laneAccount,registryAccount,entryAccount,verifierCheckpoint]))) (fun reply => NMX_R4_TryObservation.after reply (fun _unit => NMX_R4_CallScript01.t014 c.owners (ops c) verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount))) = _
 apply NMX_R4_ObservedStep.child
 intro _unit
 exact NMX_R4_Observed01.e014 c verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount
#print axioms e013

theorem e012 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript01.t012 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p012 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) := by
 unfold NMX_R4_CallScript01.t012 NMX_Fold01.p012
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.readonlyAccount laneAccount pool)) (fun reply => NMX_R4_TryObservation.after reply (fun _unit => NMX_R4_CallScript01.t013 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))) = _
 apply NMX_R4_ObservedStep.child
 intro _unit
 exact NMX_R4_Observed01.e013 c verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e012

theorem e011 (c : Context) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 observe c (NMX_R4_CallScript01.t011 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Fold01.p011 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) := by
 unfold NMX_R4_CallScript01.t011 NMX_Fold01.p011
 change observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child (.readonlyAccount checkpointAccount pool)) (fun reply => NMX_R4_TryObservation.after reply (fun _unit => NMX_R4_CallScript01.t012 c.owners (ops c) verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint))) = _
 apply NMX_R4_ObservedStep.child
 intro _unit
 exact NMX_R4_Observed01.e012 c verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e011
end NMX_R4_Observed01
end
