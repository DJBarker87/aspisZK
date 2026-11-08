import NMX_R8_Children241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_GroupSource241
open Aeneas Aeneas.Std Result AdapterRw

/-- Kernel equality for the sole block grouping. All surrounding actual
emitted conditions, Try branches and child arguments remain literal. -/
theorem source (choices : NMX_R4_Authentication.Choices) (ops : Ops)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_Effect241.stage2 ops (NMX_R8_Children241.original choices) p accounts data slot =
 NMX_R8_Code241.body ops (NMX_R8_Children241.grouped choices) p accounts data slot := by
 unfold NMS_Effect241.stage2 NMX_R8_Code241.body NMX_R8_Children241.original
 repeat' first
 | exact NMX_R8_CodecGroup.context _ _
 | rfl
 | apply congrArg (RSL.Spec.bind _)
 | split
 | funext value

#print axioms source
end NMX_R8_GroupSource241
end
