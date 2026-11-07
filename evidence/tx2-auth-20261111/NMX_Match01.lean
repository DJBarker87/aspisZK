import NMX_BindCongruence
import NMX_PdaMap
import NMX_Actual01
import NMX_Fold01
import NMX_Match02
set_option autoImplicit false
noncomputable section
namespace NMX_Match01
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_ResultSteps

/-- Actual emitted occurrence 20; complete arbitrary reply/control arms. -/
theorem e020 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Fold01.v020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey =
 NMX_Actual01.t020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey := by
 unfold NMX_Fold01.v020 NMX_Actual01.t020
 apply NMX_BindCongruence.step
 intro allLanes
 exact NMX_Match02.e021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes
#print axioms e020

/-- Actual emitted occurrence 19; complete arbitrary reply/control arms. -/
theorem e019 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) :
 NMX_Fold01.v019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster =
 NMX_Actual01.t019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey wrongMaster := by
 unfold NMX_Fold01.v019 NMX_Actual01.t019
 by_cases condition : (wrongMaster) = true
 · simp only [condition,↓reduceIte]
 · simp only [condition,↓reduceIte]
   exact NMX_Match01.e020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e019

/-- Actual emitted occurrence 18; complete arbitrary reply/control arms. -/
theorem e018 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) :
 NMX_Fold01.v018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes =
 NMX_Actual01.t018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey masterKeyBytes := by
 unfold NMX_Fold01.v018 NMX_Actual01.t018
 apply NMX_BindCongruence.step
 intro wrongMaster
 exact NMX_Match01.e019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster
#print axioms e018

/-- Actual emitted occurrence 17; complete arbitrary reply/control arms. -/
theorem e017 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_Fold01.v017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey =
 NMX_Actual01.t017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload masterKey := by
 unfold NMX_Fold01.v017 NMX_Actual01.t017
 apply NMX_BindCongruence.step
 intro masterKeyBytes
 exact NMX_Match01.e018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes
#print axioms e017

/-- Actual emitted occurrence 16; complete arbitrary reply/control arms. -/
theorem e016 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) :
 NMX_Fold01.v016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master =
 NMX_Actual01.t016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master.payload := by
 unfold NMX_Fold01.v016 NMX_Actual01.t016
 apply NMX_BindCongruence.step
 intro masterKey
 exact NMX_Match01.e017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey
#print axioms e016

/-- Actual emitted occurrence 15; complete arbitrary reply/control arms. -/
theorem e015 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) :
 NMX_Fold01.v015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes =
 NMX_Actual01.t015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes := by
 unfold NMX_Fold01.v015 NMX_Actual01.t015
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok value =>
   let master : Box Master := ⟨owners.master,value⟩
   exact NMX_Match01.e016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master
#print axioms e015

/-- Actual emitted occurrence 14; complete arbitrary reply/control arms. -/
theorem e014 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold01.v014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount =
 NMX_Actual01.t014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount := by
 unfold NMX_Fold01.v014 NMX_Actual01.t014
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok masterBytes =>
   exact NMX_Match01.e015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes
#print axioms e014

/-- Actual emitted occurrence 13; complete arbitrary reply/control arms. -/
theorem e013 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold01.v013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint =
 NMX_Actual01.t013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold NMX_Fold01.v013 NMX_Actual01.t013
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok unit =>
   exact NMX_Match01.e014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount
#print axioms e013

/-- Actual emitted occurrence 12; complete arbitrary reply/control arms. -/
theorem e012 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold01.v012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint =
 NMX_Actual01.t012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold NMX_Fold01.v012 NMX_Actual01.t012
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok unit =>
   exact NMX_Match01.e013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e012

/-- Actual emitted occurrence 11; complete arbitrary reply/control arms. -/
theorem e011 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_Fold01.v011 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint =
 NMX_Actual01.t011 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold NMX_Fold01.v011 NMX_Actual01.t011
 unfold tryThen
 apply NMX_BindCongruence.step
 intro reply
 cases reply with
 | Err error => rfl
 | Ok unit =>
   exact NMX_Match01.e012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint
#print axioms e011
end NMX_Match01
end
