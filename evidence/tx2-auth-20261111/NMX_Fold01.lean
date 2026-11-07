import NMX_S011
import NMX_S012
import NMX_S013
import NMX_S014
import NMX_S015
import NMX_S016
import NMX_S017
import NMX_S018
import NMX_S019
import NMX_S020
import NMX_Fold02
set_option autoImplicit false
noncomputable section
namespace NMX_Fold01
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps

def p020 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw ops.op16) (fun allLanes =>
  NMX_Fold02.p021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes)
def v020 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Final :=
  (ops.op16) >>= fun value => (fun allLanes =>
  NMX_Fold02.v021 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey allLanes) value
theorem e020 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) ()) =
 v020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey := by
 unfold p020 v020
 rw [NMX_S020.step]
 simp only [NMX_Fold02.e021]
#print axioms e020

def p019 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongMaster) (fun _unit =>
  NMX_Fold01.p020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)
def v019 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) : Final :=
  if wrongMaster then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold01.v020 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) ()
theorem e019 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (wrongMaster : Bool) :
 NMX_ValueLink.erase (eval (source ops owners) (p019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster) ()) =
 v019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster := by
 unfold p019 v019
 rw [NMX_S019.step]
 simp only [NMX_Fold01.e020]
#print axioms e019

def p018 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  master.payload.identity.pool masterKeyBytes)) (fun wrongMaster =>
  NMX_Fold01.p019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster)
def v018 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) : Final :=
  ((core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  master.payload.identity.pool masterKeyBytes)) >>= fun value => (fun wrongMaster =>
  NMX_Fold01.v019 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey wrongMaster) value
theorem e018 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (masterKeyBytes : Array U8 32#usize) :
 NMX_ValueLink.erase (eval (source ops owners) (p018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes) ()) =
 v018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes := by
 unfold p018 v018
 rw [NMX_S018.step]
 simp only [NMX_Fold01.e019]
#print axioms e018

def p017 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun masterKeyBytes =>
  NMX_Fold01.p018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes)
def v017 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) : Final :=
  (ops.op39 masterKey) >>= fun value => (fun masterKeyBytes =>
  NMX_Fold01.v018 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey masterKeyBytes) value
theorem e017 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) ()) =
 v017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey := by
 unfold p017 v017
 rw [NMX_S017.step]
 simp only [NMX_Fold01.e018]
#print axioms e017

def p016 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.key masterAccount)) (fun masterKey =>
  NMX_Fold01.p017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey)
def v016 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) : Final :=
  (r1_pool_adapter.owned.OwnedAccount.impl.key masterAccount) >>= fun value => (fun masterKey =>
  NMX_Fold01.v017 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master masterKey) value
theorem e016 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) :
 NMX_ValueLink.erase (eval (source ops owners) (p016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master) ()) =
 v016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master := by
 unfold p016 v016
 rw [NMX_S016.step]
 simp only [NMX_Fold01.e017]
#print axioms e016

def p015 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.master masterBytes)) (fun master =>
  NMX_Fold01.p016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master)
def v015 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) : Final :=
  tryThen (ops.op48 masterBytes) (fun value => (fun master =>
  NMX_Fold01.v016 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount master) ⟨owners.master,value⟩)
theorem e015 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (masterBytes : Slice U8) :
 NMX_ValueLink.erase (eval (source ops owners) (p015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes) ()) =
 v015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes := by
 unfold p015 v015
 rw [NMX_S015.step]
 simp only [NMX_Fold01.e016]
#print axioms e015

def p014 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.data masterAccount)) (fun masterBytes =>
  NMX_Fold01.p015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes)
def v014 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) : Final :=
  tryThen (r1_pool_adapter.owned.OwnedAccount.data ops masterAccount) (fun value => (fun masterBytes =>
  NMX_Fold01.v015 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount masterBytes) value)
theorem e014 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount) ()) =
 v014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount := by
 unfold p014 v014
 rw [NMX_S014.step]
 simp only [NMX_Fold01.e015]
#print axioms e014

def p013 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.distinct (Array.make 7#usize [proof,masterAccount,checkpointAccount,
  laneAccount,registryAccount,entryAccount,verifierCheckpoint]))) (fun _unit =>
  NMX_Fold01.p014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount)
def v013 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final :=
  tryThen (r1_pool_adapter.owned.require_distinct_accounts ops (Array.make 7#usize [proof,masterAccount,checkpointAccount,
  laneAccount,registryAccount,entryAccount,verifierCheckpoint])) (fun value => (fun value =>
  NMX_Fold01.v014 owners ops verifier pool outputLane slot masterAccount checkpointAccount laneAccount registryAccount entryAccount) value)
theorem e013 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) ()) =
 v013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold p013 v013
 rw [NMX_S013.step]
 simp only [NMX_Fold01.e014]
#print axioms e013

def p012 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.readonlyAccount laneAccount pool)) (fun _unit =>
  NMX_Fold01.p013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)
def v012 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final :=
  tryThen (r1_pool_adapter.owned.require_readonly_account ops laneAccount pool) (fun value => (fun value =>
  NMX_Fold01.v013 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) value)
theorem e012 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) ()) =
 v012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold p012 v012
 rw [NMX_S012.step]
 simp only [NMX_Fold01.e013]
#print axioms e012

def p011 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.readonlyAccount checkpointAccount pool)) (fun _unit =>
  NMX_Fold01.p012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)
def v011 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Final :=
  tryThen (r1_pool_adapter.owned.require_readonly_account ops checkpointAccount pool) (fun value => (fun value =>
  NMX_Fold01.v012 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) value)
theorem e011 (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) :
 NMX_ValueLink.erase (eval (source ops owners) (p011 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint) ()) =
 v011 owners ops verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint := by
 unfold p011 v011
 rw [NMX_S011.step]
 simp only [NMX_Fold01.e012]
#print axioms e011
end NMX_Fold01
end
