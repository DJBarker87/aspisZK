import NMS_R2RequestFactor242
import NMS_R2RequestGuards
import NMS_R2N_Native242Children
set_option autoImplicit false
noncomputable section
namespace NMS_R2Gated242
open Aeneas Aeneas.Std Result AdapterRw
open NMS_Effect242 (Effects AuthCall)
open NMS_R2Code242Factor (afterAuth)
def afterGuards (effects : Effects RSL.Spec) (auth : AuthCall RSL.Spec)
 (verifier_program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (current_slot : core.result.Result U64 solana_program_error.ProgramError)
 (request : NMS_R2RequestBindings.Request) :
 RSL.Spec (core.result.Result r1_pool_adapter.ValidatedAsqa solana_program_error.ProgramError) := do
 let pool_program ←
   effects.op37 request.pool_program
 let a1 ←
   effects.op20
     request.«public»
 let r2 ←
   effects.op17
     a1
 let r3 ←
   core.result.Result.map_err
     r1_pool_adapter.owned.validate_asq8.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestAccountErrorV1ProgramError
     r2 ()
 let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
 match cf1 with
 | core.ops.control_flow.ControlFlow.Continue val1 =>
   let cf2 ←
     core.result.Result.Insts.CoreOpsTry.branch current_slot
   match cf2 with
   | core.ops.control_flow.ControlFlow.Continue val2 =>
     let r4 ←
       auth
         verifier_program accounts pool_program val1 val2
     let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
     match cf3 with
     | core.ops.control_flow.ControlFlow.Continue val3 =>
       afterAuth effects request val3 accounts
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
         solana_program_error.ProgramError) residual
   | core.ops.control_flow.ControlFlow.Break residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
       solana_program_error.ProgramError) residual
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_pool_adapter.ValidatedAsqa (core.convert.FromSame
     solana_program_error.ProgramError) residual

theorem source (devnet : Bool) (auth : AuthCall RSL.Spec)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (slot : core.result.Result U64 solana_program_error.ProgramError) (q : NMS_R2RequestBindings.Request) :
 NMS_R2RequestFactor242.afterRequest (NMS_R2N_Native242Children.children devnet) auth program accounts slot q =
 NMS_R2RequestGuards.actual q devnet
  (afterGuards (NMS_R2N_Native242Children.children devnet) auth program accounts slot q) := rfl

theorem checked (devnet : Bool) (auth : AuthCall RSL.Spec)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (slot : core.result.Result U64 solana_program_error.ProgramError) (q : NMS_R2RequestBindings.Request) :
 NMS_R2RequestFactor242.afterRequest (NMS_R2N_Native242Children.children devnet) auth program accounts slot q =
 if NMS_R2RequestGuards.bad q devnet then RSL.Spec.pure (.Err .InvalidInstructionData)
 else afterGuards (NMS_R2N_Native242Children.children devnet) auth program accounts slot q := by
 rw [source,NMS_R2RequestGuards.source]
#print axioms source
#print axioms checked
end NMS_R2Gated242
