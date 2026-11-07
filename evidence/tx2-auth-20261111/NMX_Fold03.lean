import NMX_S031
import NMX_S032
import NMX_S033
import NMX_S034
import NMX_S035
import NMX_S036
import NMX_S037
import NMX_S038
import NMX_S039
import NMX_S040
import NMX_Fold04
set_option autoImplicit false
noncomputable section
namespace NMX_Fold03
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceModel NMX_ResultSteps

def p040 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.data laneAccount)) (fun laneBytes =>
  NMX_Fold04.p041 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes)
def v040 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) : Final :=
  tryThen (r1_pool_adapter.owned.OwnedAccount.data ops laneAccount) (fun value => (fun laneBytes =>
  NMX_Fold04.v041 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey laneBytes) value)
theorem e040 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p040 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey) ()) =
 v040 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey := by
 unfold p040 v040
 rw [NMX_S040.step]
 simp only [NMX_Fold04.e041]
#print axioms e040

def p039 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongCheckpointPda) (fun _unit =>
  NMX_Fold03.p040 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey)
def v039 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) : Final :=
  if wrongCheckpointPda then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold03.v040 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey) ()
theorem e039 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointKey : solana_pubkey.Pubkey) (wrongCheckpointPda : Bool) :
 NMX_ValueLink.erase (eval (source ops owners) (p039 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda) ()) =
 v039 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda := by
 unfold p039 v039
 rw [NMX_S039.step]
 simp only [NMX_Fold03.e040]
#print axioms e039

def p038 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedCheckpoint checkpointKey)) (fun wrongCheckpointPda =>
  NMX_Fold03.p039 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda)
def v038 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) : Final :=
  ((core.cmp.PartialEq.ne.trait_default
  (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) derivedCheckpoint checkpointKey)) >>= fun value => (fun wrongCheckpointPda =>
  NMX_Fold03.v039 owners ops pool outputLane laneAccount master masterKey checkpoint checkpointKey wrongCheckpointPda) value
theorem e038 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) (checkpointKey : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p038 owners ops pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey) ()) =
 v038 owners ops pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey := by
 unfold p038 v038
 rw [NMX_S038.step]
 simp only [NMX_Fold03.e039]
#print axioms e038

def p037 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.key checkpointAccount)) (fun checkpointKey =>
  NMX_Fold03.p038 owners ops pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey)
def v037 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) : Final :=
  (r1_pool_adapter.owned.OwnedAccount.impl.key checkpointAccount) >>= fun value => (fun checkpointKey =>
  NMX_Fold03.v038 owners ops pool outputLane laneAccount master masterKey checkpoint derivedCheckpoint checkpointKey) value
theorem e037 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (derivedCheckpoint : solana_pubkey.Pubkey) :
 NMX_ValueLink.erase (eval (source ops owners) (p037 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint) ()) =
 v037 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint := by
 unfold p037 v037
 rw [NMX_S037.step]
 simp only [NMX_Fold03.e038]
#print axioms e037

def p036 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.pda checkpointSeeds pool)) (fun derivedCheckpoint =>
  NMX_Fold03.p037 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint)
def v036 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) : Final :=
  tryThen (do let reply ← ops.op38 checkpointSeeds pool; match reply with | .Ok key => ok (.Ok key) | .Err _ => ok (.Err .InvalidAccountData)) (fun value => (fun derivedCheckpoint =>
  NMX_Fold03.v037 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint derivedCheckpoint) value)
theorem e036 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointSeeds : Slice (Slice U8)) :
 NMX_ValueLink.erase (eval (source ops owners) (p036 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds) ()) =
 v036 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds := by
 unfold p036 v036
 rw [NMX_S036.step]
 simp only [NMX_Fold03.e037]
#print axioms e036

def p035 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.asRef masterKey)) (fun checkpointMasterSeed =>
  let sequenceSeed := Array.to_slice (core.num.U64.to_le_bytes checkpoint.payload.checkpoint_sequence)
  let checkpointBump := Array.to_slice (Array.make 1#usize [checkpoint.payload.bump])
  let checkpointSeeds := Array.to_slice (Array.make 4#usize [
    r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,checkpointMasterSeed,sequenceSeed,checkpointBump])
  NMX_Fold03.p036 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds)
def v035 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Final :=
  (ops.op40 masterKey) >>= fun value => (fun checkpointMasterSeed =>
  let sequenceSeed := Array.to_slice (core.num.U64.to_le_bytes checkpoint.payload.checkpoint_sequence)
  let checkpointBump := Array.to_slice (Array.make 1#usize [checkpoint.payload.bump])
  let checkpointSeeds := Array.to_slice (Array.make 4#usize [
    r1_pool_adapter.PAIR_FOREST_CHECKPOINT_SEED,checkpointMasterSeed,sequenceSeed,checkpointBump])
  NMX_Fold03.v036 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointSeeds) value
theorem e035 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_ValueLink.erase (eval (source ops owners) (p035 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint) ()) =
 v035 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint := by
 unfold p035 v035
 rw [NMX_S035.step]
 simp only [NMX_Fold03.e036]
#print axioms e035

def p034 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongDeployment) (fun _unit =>
  NMX_Fold03.p035 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint)
def v034 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) : Final :=
  if wrongDeployment then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold03.v035 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint) ()
theorem e034 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongDeployment : Bool) :
 NMX_ValueLink.erase (eval (source ops owners) (p034 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment) ()) =
 v034 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment := by
 unfold p034 v034
 rw [NMX_S034.step]
 simp only [NMX_Fold03.e035]
#print axioms e034

def p033 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  checkpoint.payload.deployment_domain master.payload.identity.deployment_domain)) (fun wrongDeployment =>
  NMX_Fold03.p034 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment)
def v033 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) : Final :=
  ((core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  checkpoint.payload.deployment_domain master.payload.identity.deployment_domain)) >>= fun value => (fun wrongDeployment =>
  NMX_Fold03.v034 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongDeployment) value
theorem e033 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) :
 NMX_ValueLink.erase (eval (source ops owners) (p033 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint) ()) =
 v033 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint := by
 unfold p033 v033
 rw [NMX_S033.step]
 simp only [NMX_Fold03.e034]
#print axioms e033

def p032 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.check wrongCheckpointMaster) (fun _unit =>
  NMX_Fold03.p033 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint)
def v032 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) : Final :=
  if wrongCheckpointMaster then ok (.Err .InvalidAccountData) else (fun value =>
  NMX_Fold03.v033 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint) ()
theorem e032 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (wrongCheckpointMaster : Bool) :
 NMX_ValueLink.erase (eval (source ops owners) (p032 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster) ()) =
 v032 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster := by
 unfold p032 v032
 rw [NMX_S032.step]
 simp only [NMX_Fold03.e033]
#print axioms e032

def p031 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  checkpoint.payload.master checkpointMasterBytes)) (fun wrongCheckpointMaster =>
  NMX_Fold03.p032 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster)
def v031 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) : Final :=
  ((core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
  checkpoint.payload.master checkpointMasterBytes)) >>= fun value => (fun wrongCheckpointMaster =>
  NMX_Fold03.v032 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint wrongCheckpointMaster) value
theorem e031 (owners : Owners) (ops : Ops) (pool : solana_pubkey.Pubkey) (outputLane : U8) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (master : Box Master) (masterKey : solana_pubkey.Pubkey) (checkpoint : Box Checkpoint) (checkpointMasterBytes : Array U8 32#usize) :
 NMX_ValueLink.erase (eval (source ops owners) (p031 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes) ()) =
 v031 owners ops pool outputLane checkpointAccount laneAccount master masterKey checkpoint checkpointMasterBytes := by
 unfold p031 v031
 rw [NMX_S031.step]
 simp only [NMX_Fold03.e032]
#print axioms e031
end NMX_Fold03
end
