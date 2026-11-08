import NMX_R4_CallScript00
import NMX_R4_CallRun
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallRoot
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallProgram

def auth (owners : Owners) (ops : Ops) (verifier : solana_pubkey.Pubkey)
 (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (pool : solana_pubkey.Pubkey)
 (outputLane : U8) (slot : U64) : Program (core.result.Result Auth PE) :=
 if Slice.len accounts = 7#usize then
 NMX_R4_CallScript00.t001 owners ops verifier accounts pool outputLane slot
 else if Slice.len accounts < 7#usize then .ret (.Err .NotEnoughAccountKeys)
 else .ret (.Err .InvalidArgument)
end NMX_R4_CallRoot
end
