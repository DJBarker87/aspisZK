import NMX_S041
import NMX_S042
import NMX_S043
import NMX_S044
import NMX_S045
import NMX_S046
import NMX_S047
import NMX_S048
import NMX_S049
import NMX_S050
import NMX_UnusedWitnesses
import NMX_Fold05
set_option autoImplicit false
noncomputable section
namespace NMX_Fold04
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps

def p050 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongLanePda) (fun _unit =>
  NMX_Fold05.p051 owners ops master masterKey checkpoint checkpointKey lane laneKey)
def v050 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) : Final :=
  if wrongLanePda then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold05.v051 owners ops master masterKey checkpoint checkpointKey lane laneKey) ()
theorem e050 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneKey : solana_pubkey.Pubkey) (wrongLanePda : Bool) :
 NMX_ValueLink.erase (eval (source ops owners) (p050 owners ops master masterKey checkpoint checkpointKey lane laneKey wrongLanePda) ()) =
 v050 owners ops master masterKey checkpoint checkpointKey lane laneKey wrongLanePda := by
 unfold p050 v050
 rw [NMX_S050.step ops owners wrongLanePda]
 simp only [NMX_Fold05.e051] <;> rfl
#print axioms e050

def p049 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedLane laneKey)) (fun wrongLanePda =>
  NMX_Fold04.p050 owners ops master masterKey checkpoint checkpointKey lane laneKey wrongLanePda)
def v049 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) : Final :=
  ((core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedLane laneKey)) >>= fun value => (fun wrongLanePda =>
  NMX_Fold04.v050 owners ops master masterKey checkpoint checkpointKey lane laneKey wrongLanePda) value
theorem e049 (owners : Owners) (ops : Ops) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) (laneKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p049 owners ops master masterKey checkpoint checkpointKey lane derivedLane laneKey) ()) =
 v049 owners ops master masterKey checkpoint checkpointKey lane derivedLane laneKey := by
 unfold p049 v049
 rw [NMX_S049.step ops owners derivedLane laneKey]
 simp only [NMX_Fold04.e050] <;> rfl
#print axioms e049

def p048 (owners : Owners) (ops : Ops) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.key laneAccount)) (fun laneKey =>
  NMX_Fold04.p049 owners ops master masterKey checkpoint checkpointKey lane derivedLane laneKey)
def v048 (owners : Owners) (ops : Ops) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) : Final :=
  (r1_pool_adapter.owned.OwnedAccount.impl.key laneAccount) >>= fun value => (fun laneKey =>
  NMX_Fold04.v049 owners ops master masterKey checkpoint checkpointKey lane derivedLane laneKey) value
theorem e048 (owners : Owners) (ops : Ops) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (derivedLane : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p048 owners ops laneAccount master masterKey checkpoint checkpointKey lane derivedLane) ()) =
 v048 owners ops laneAccount master masterKey checkpoint checkpointKey lane derivedLane := by
 unfold p048 v048
 rw [NMX_S048.step ops owners laneAccount]
 simp only [NMX_Fold04.e049] <;> rfl
#print axioms e048

def p047 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.pda laneSeeds pool)) (fun derivedLane =>
  NMX_Fold04.p048 owners ops laneAccount master masterKey checkpoint checkpointKey lane derivedLane)
def v047 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) : Final :=
  tryThen (do let reply ← ops.op38 laneSeeds pool; match reply with | .Ok key => ok (.Ok key) | .Err _ => ok (.Err .InvalidAccountData)) (fun value => (fun derivedLane =>
  NMX_Fold04.v048 owners ops laneAccount master masterKey checkpoint checkpointKey lane derivedLane) value)
theorem e047 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneSeeds : Slice (Slice U8)) :
 NMX_ValueLink.erase (eval (source ops owners) (p047 owners ops pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds) ()) =
 v047 owners ops pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds := by
 unfold p047 v047
 rw [NMX_S047.step ops owners pool laneSeeds]
 simp only [NMX_Fold04.e048] <;> rfl
#print axioms e047

def p046 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.asRef masterKey)) (fun laneMasterSeed =>
  let laneIdSeed := Array.to_slice (Array.make 1#usize [outputLane])
  let laneBump := Array.to_slice (Array.make 1#usize [lane.payload.bump])
  let laneSeeds := Array.to_slice (Array.make 4#usize [
    r1_pool_adapter.PAIR_FOREST_LANE_SEED,laneMasterSeed,laneIdSeed,laneBump])
  NMX_Fold04.p047 owners ops pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds)
def v046 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Final :=
  (ops.op40 masterKey) >>= fun value => (fun laneMasterSeed =>
  let laneIdSeed := Array.to_slice (Array.make 1#usize [outputLane])
  let laneBump := Array.to_slice (Array.make 1#usize [lane.payload.bump])
  let laneSeeds := Array.to_slice (Array.make 4#usize [
    r1_pool_adapter.PAIR_FOREST_LANE_SEED,laneMasterSeed,laneIdSeed,laneBump])
  NMX_Fold04.v047 owners ops pool laneAccount master masterKey checkpoint checkpointKey lane laneSeeds) value
theorem e046 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_ValueLink.erase (eval (source ops owners) (p046 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) ()) =
 v046 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane := by
 unfold p046 v046
 rw [NMX_S046.step ops owners masterKey]
 simp only [NMX_Fold04.e047] <;> rfl
#print axioms e046

def p045 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check (lane.payload.lane_id != outputLane)) (fun _unit =>
  NMX_Fold04.p046 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)
def v045 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Final :=
  if (lane.payload.lane_id != outputLane) then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold04.v046 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) ()
theorem e045 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_ValueLink.erase (eval (source ops owners) (p045 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) ()) =
 v045 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane := by
 unfold p045 v045
 rw [NMX_S045.step ops owners outputLane lane]
 simp only [NMX_Fold04.e046] <;> rfl
#print axioms e045

def p044 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongLaneMaster) (fun _unit =>
  NMX_Fold04.p045 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)
def v044 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) : Final :=
  if wrongLaneMaster then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold04.v045 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) ()
theorem e044 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (wrongLaneMaster : Bool) :
 NMX_ValueLink.erase (eval (source ops owners) (p044 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster) ()) =
 v044 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster := by
 unfold p044 v044
 rw [NMX_S044.step ops owners wrongLaneMaster]
 simp only [NMX_Fold04.e045] <;> rfl
#print axioms e044

def p043 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  lane.payload.master laneMasterBytes)) (fun wrongLaneMaster =>
  NMX_Fold04.p044 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster)
def v043 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) : Final :=
  ((core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  lane.payload.master laneMasterBytes)) >>= fun value => (fun wrongLaneMaster =>
  NMX_Fold04.v044 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane wrongLaneMaster) value
theorem e043 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) (laneMasterBytes : Array U8 32#usize) :
 NMX_ValueLink.erase (eval (source ops owners) (p043 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes) ()) =
 v043 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes := by
 unfold p043 v043
 rw [NMX_S043.step ops owners laneMasterBytes master lane]
 simp only [NMX_Fold04.e044] <;> rfl
#print axioms e043

def p042 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.toBytes masterKey)) (fun laneMasterBytes =>
  NMX_Fold04.p043 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes)
def v042 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) : Final :=
  (ops.op39 masterKey) >>= fun value => (fun laneMasterBytes =>
  NMX_Fold04.v043 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane laneMasterBytes) value
theorem e042 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (lane : Box Lane) :
 NMX_ValueLink.erase (eval (source ops owners) (p042 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) ()) =
 v042 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane := by
 unfold p042 v042
 rw [NMX_S042.step ops owners masterKey]
 simp only [NMX_Fold04.e043] <;> rfl
#print axioms e042

def p041 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.lane laneBytes)) (fun lane =>
  NMX_Fold04.p042 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane)
def v041 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) : Final :=
  tryThen (ops.op50 laneBytes) (fun value => (fun lane =>
  NMX_Fold04.v042 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey lane) ⟨owners.lane,value⟩)
theorem e041 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (laneBytes : Slice U8) :
 NMX_ValueLink.erase (eval (source ops owners) (p041 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes) ()) =
 v041 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes := by
 unfold p041 v041
 rw [NMX_S041.step ops owners laneBytes NMX_UnusedWitnesses.lane]
 simp only [NMX_Fold04.e042] <;> rfl
#print axioms e041
end NMX_Fold04
end
