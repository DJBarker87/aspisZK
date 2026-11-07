import NMX_Skeleton
import NMX_SF01
set_option autoImplicit false
noncomputable section
namespace NMX_SF00
open Aeneas Aeneas.Std AdapterRw NMX_OwnedPackets NMX_Program NMX_SourceProgram
attribute [local instance] Classical.propDecidable

def p010 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.readonlyAccount masterAccount pool)) (fun _unit =>
  NMX_SF01.p011 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def p009 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.checkpointGuard verifierCheckpoint verifier false)) (fun _unit =>
  NMX_SF00.p010 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def p008 (verifier : solana_pubkey.Pubkey) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) (verifierCheckpoint : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.call (.readonlyBuffer proof)) (fun _unit =>
  NMX_SF00.p009 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def p007 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) (entryAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 6#usize)) (fun verifierCheckpoint =>
  NMX_SF00.p008 verifier pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount verifierCheckpoint)

def p006 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) (registryAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 5#usize)) (fun entryAccount =>
  NMX_SF00.p007 verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount entryAccount)

def p005 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) (laneAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 4#usize)) (fun registryAccount =>
  NMX_SF00.p006 verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount registryAccount)

def p004 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) (checkpointAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 3#usize)) (fun laneAccount =>
  NMX_SF00.p005 verifier accounts pool outputLane slot proof masterAccount checkpointAccount laneAccount)

def p003 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) (masterAccount : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 2#usize)) (fun checkpointAccount =>
  NMX_SF00.p004 verifier accounts pool outputLane slot proof masterAccount checkpointAccount)

def p002 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) (proof : r1_pool_adapter.owned.OwnedAccount) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 1#usize)) (fun masterAccount =>
  NMX_SF00.p003 verifier accounts pool outputLane slot proof masterAccount)

def p001 (verifier : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey) (outputLane : U8) (slot : U64) : Program Auth :=
 NMX_Program.bind (NMX_SourceProgram.raw (Slice.index_usize accounts 0#usize)) (fun proof =>
  NMX_SF00.p002 verifier accounts pool outputLane slot proof)
end NMX_SF00
end
