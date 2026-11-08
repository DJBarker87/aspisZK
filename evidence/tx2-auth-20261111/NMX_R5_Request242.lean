import NMX_R5_Guards242
set_option autoImplicit false
noncomputable section
namespace NMX_R5_Request242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed

def bad (q : LIBB_PoolCarriers.Request) : Bool :=
 decide (L.reqProfile q ≠ RSL.PROFILE_BINDING) || decide (L.reqRelease q ≠ RSL.RELEASE_BINDING) ||
 decide (L.reqPoolProgram q ≠ D.pool)

def model (q : LIBB_PoolCarriers.Request) (program : RSL.B32)
 (accounts : List RSL.OwnedAccount) (slot : Except RSL.ProgramError UInt64) :=
 RSL.RS.seq (RSL.RS.check (bad q) .invalidInstructionData)
  (NMX_R5_Guards242.model q program accounts slot)

theorem guard (q : LIBB_PoolCarriers.Request) : NMS_R2RequestGuards.bad q false = bad q := rfl

theorem full (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (q : LIBB_PoolCarriers.Request) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (NMS_R2RequestFactor242.afterRequest (NMS_R2N_Native242Children.children false)
   (NMX_R4_NMS233.typed choices) program accounts slot q)
  (model q (NMS_R2N_RSLScalars.b32 program) (NMS_R2N_RSLPoolCarriers.accounts accounts)
   (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 slot)) := by
 rw [NMS_R2Gated242.source]
 have h := NMS_R2RequestGuards.full NMX_R5_AfterAuth242.value q false _ _
  (NMX_R5_Guards242.full choices program accounts q slot)
 simpa only [model,guard] using h
#print axioms guard
#print axioms full
end NMX_R5_Request242
end
