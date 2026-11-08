import NMX_R5_LaneSource242
set_option autoImplicit false
noncomputable section
namespace NMX_R5_Slot242
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed

def source (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (q : LIBB_PoolCarriers.Request) (lane : U8)
 (slot : core.result.Result U64 solana_program_error.ProgramError) :
 RSL.Spec (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError) := do
 let flow ← core.result.Result.Insts.CoreOpsTry.branch slot
 match flow with
 | .Continue current =>
   NMS_R2N_RawTry.literal (NMX_R4_NMS233.typed choices program accounts q.pool_program lane current)
    (fun authenticated => NMS_R2Code242Factor.afterAuth (NMS_R2N_Native242Children.children false) q authenticated accounts)
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    r1_pool_adapter.ValidatedAsqa (core.convert.FromSame solana_program_error.ProgramError) residual

def model (q : LIBB_PoolCarriers.Request) (program : RSL.B32)
 (accounts : List RSL.OwnedAccount) (lane : UInt8) (slot : Except RSL.ProgramError UInt64) :
 RSL.RS (RSL.TX2_242.Validated L) :=
 RSL.RS.bind (RSL.RS.ofExcept slot) fun current =>
 RSL.RS.bind (RSL.Spec.call RSL.TX2_233.Domain (RSL.TX2_233.Ref L D)
  ⟨program,accounts,L.reqPoolProgram q,lane,current⟩) fun authenticated =>
 NMX_R5_AfterAuth242.model q authenticated accounts

theorem full (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (q : LIBB_PoolCarriers.Request) (lane : U8)
 (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Simulates (NMS_R2N_RSLError.reply NMX_R5_AfterAuth242.value)
  (source choices program accounts q lane slot)
  (model q (NMS_R2N_RSLScalars.b32 program) (NMS_R2N_RSLPoolCarriers.accounts accounts)
   (NMS_R2N_RSLScalars.u8 lane) (NMS_R2N_RSLError.reply NMS_R2N_RSLScalars.u64 slot)) := by
 unfold source model
 cases slot with
 | Err e =>
   change Simulates _ (RSL.Spec.bind (RSL.Spec.pure _) _) _
   rw [RSL.Spec.bind_pure]
   change Simulates _ (RSL.Spec.pure (core.result.Result.Err e : core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError))
    (RSL.RS.bind (RSL.RS.throw (NMS_R2N_RSLError.error e)) _)
   rw [RSL.RS.bind_throw]
   exact NMS_R2N_Interpreted.pure _ _
 | Ok current =>
   change Simulates _ (RSL.Spec.bind (RSL.Spec.pure _) _) _
   rw [RSL.Spec.bind_pure]
   change Simulates _ _ (RSL.RS.bind (RSL.RS.pure (NMS_R2N_RSLScalars.u64 current)) _)
   rw [RSL.RS.bind_pure]
   apply NMS_R2N_RawTry.simulates NMS_R2N_RSLPoolCarriers.authenticated NMX_R5_AfterAuth242.value
   · intro env o invocation
     exact ⟨trivial,NMX_R4_NMS233.packet choices program accounts q.pool_program lane current env o invocation⟩
   · intro authenticated
     exact NMX_R5_AfterAuth242.full q authenticated accounts
#print axioms full
end NMX_R5_Slot242
end
