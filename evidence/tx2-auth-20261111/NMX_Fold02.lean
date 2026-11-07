import NMX_S021
import NMX_S022
import NMX_S023
import NMX_S024
import NMX_S025
import NMX_S026
import NMX_S027
import NMX_S028
import NMX_S029
import NMX_S030
import NMX_Fold03
set_option autoImplicit false
noncomputable section
namespace NMX_Fold02
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps

def p030 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun checkpointMasterBytes =>
  NMX_Fold03.p031 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes)
def v030 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Final :=
  (ops.op39 masterKey) >>= fun value => (fun checkpointMasterBytes =>
  NMX_Fold03.v031 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes) value
theorem e030 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_ValueLink.erase (eval (source ops owners) (p030 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint) ()) =
 v030 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint := by
 unfold p030 v030
 rw [NMX_S030.step]
 simp only [NMX_Fold03.e031]
#print axioms e030

def p029 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.checkpoint checkpointBytes)) (fun checkpoint =>
  NMX_Fold02.p030 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint)
def v029 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) : Final :=
  tryThen (ops.op49 checkpointBytes) (fun value => (fun checkpoint =>
  NMX_Fold02.v030 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint) ⟨owners.checkpoint,value⟩)
theorem e029 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpointBytes : Slice U8) :
 NMX_ValueLink.erase (eval (source ops owners) (p029 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes) ()) =
 v029 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes := by
 unfold p029 v029
 rw [NMX_S029.step]
 simp only [NMX_Fold02.e030]
#print axioms e029

def p028 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.data checkpointAccount)) (fun checkpointBytes =>
  NMX_Fold02.p029 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes)
def v028 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Final :=
  tryThen (r1_pool_adapter.owned.OwnedAccount.data ops checkpointAccount) (fun value => (fun checkpointBytes =>
  NMX_Fold02.v029 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpointBytes) value)
theorem e028 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p028 owners ops pool outputLane checkpointAccount laneAccount master masterKey) ()) =
 v028 owners ops pool outputLane checkpointAccount laneAccount master masterKey := by
 unfold p028 v028
 rw [NMX_S028.step]
 simp only [NMX_Fold02.e029]
#print axioms e028

def p027 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.registry verifier pool masterAccount master.payload registryAccount entryAccount slot)) (fun _unit =>
  NMX_Fold02.p028 owners ops pool outputLane checkpointAccount laneAccount master masterKey)
def v027 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Final :=
  tryThen (r1_pool_adapter.owned.authenticate_invariant_release_registry ops verifier pool masterAccount master.payload registryAccount entryAccount slot) (fun value => (fun value =>
  NMX_Fold02.v028 owners ops pool outputLane checkpointAccount laneAccount master masterKey) value)
theorem e027 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p027 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) ()) =
 v027 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey := by
 unfold p027 v027
 rw [NMX_S027.step]
 simp only [NMX_Fold02.e028]
#print axioms e027

def p026 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongMasterPda) (fun _unit =>
  NMX_Fold02.p027 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)
def v026 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) : Final :=
  if wrongMasterPda then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold02.v027 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) ()
theorem e026 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMasterPda : Bool) :
 NMX_ValueLink.erase (eval (source ops owners) (p026 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda) ()) =
 v026 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda := by
 unfold p026 v026
 rw [NMX_S026.step]
 simp only [NMX_Fold02.e027]
#print axioms e026

def p025 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedMaster masterKey)) (fun wrongMasterPda =>
  NMX_Fold02.p026 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda)
def v025 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) : Final :=
  ((core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedMaster masterKey)) >>= fun value => (fun wrongMasterPda =>
  NMX_Fold02.v026 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMasterPda) value
theorem e025 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (derivedMaster : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p025 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster) ()) =
 v025 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster := by
 unfold p025 v025
 rw [NMX_S025.step]
 simp only [NMX_Fold02.e026]
#print axioms e025

def p024 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.pda masterSeeds pool)) (fun derivedMaster =>
  NMX_Fold02.p025 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster)
def v024 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) : Final :=
  tryThen (do let reply ← ops.op38 masterSeeds pool; match reply with | .Ok key => ok (.Ok key) | .Err _ => ok (.Err .InvalidAccountData)) (fun value => (fun derivedMaster =>
  NMX_Fold02.v025 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey derivedMaster) value)
theorem e024 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterSeeds : Slice (Slice U8)) :
 NMX_ValueLink.erase (eval (source ops owners) (p024 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds) ()) =
 v024 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds := by
 unfold p024 v024
 rw [NMX_S024.step]
 simp only [NMX_Fold02.e025]
#print axioms e024

def p023 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.asRef mintKey)) (fun mintSeed =>
  let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
  let masterSeeds := Array.to_slice (Array.make 3#usize [
    r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
  NMX_Fold02.p024 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds)
def v023 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) : Final :=
  (ops.op40 mintKey) >>= fun value => (fun mintSeed =>
  let bumpSeed := Array.to_slice (Array.make 1#usize [master.payload.bump])
  let masterSeeds := Array.to_slice (Array.make 3#usize [
    r1_pool_adapter.PAIR_FOREST_MASTER_SEED,mintSeed,bumpSeed])
  NMX_Fold02.v024 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterSeeds) value
theorem e023 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (mintKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p023 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey) ()) =
 v023 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey := by
 unfold p023 v023
 rw [NMX_S023.step]
 simp only [NMX_Fold02.e024]
#print axioms e023

def p022 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.fromBytes master.payload.identity.asset_mint)) (fun mintKey =>
  NMX_Fold02.p023 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey)
def v022 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Final :=
  (ops.op37 master.payload.identity.asset_mint) >>= fun value => (fun mintKey =>
  NMX_Fold02.v023 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey mintKey) value
theorem e022 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p022 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) ()) =
 v022 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey := by
 unfold p022 v022
 rw [NMX_S022.step]
 simp only [NMX_Fold02.e023]
#print axioms e022

def p021 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check (master.payload.initialized_lane_mask != allLanes)) (fun _unit =>
  NMX_Fold02.p022 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)
def v021 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) : Final :=
  if (master.payload.initialized_lane_mask != allLanes) then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold02.v022 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) ()
theorem e021 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (allLanes : U8) :
 NMX_ValueLink.erase (eval (source ops owners) (p021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes) ()) =
 v021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes := by
 unfold p021 v021
 rw [NMX_S021.step]
 simp only [NMX_Fold02.e022]
#print axioms e021
end NMX_Fold02
end
