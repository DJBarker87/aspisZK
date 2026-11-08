import NMX_R9_After241
set_option autoImplicit false
noncomputable section
namespace NMX_R9_GroupHead241
open Aeneas Aeneas.Std Result AdapterRw

theorem source (choices : NMX_R4_Authentication.Choices) (ops : Ops)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 NMS_Effect241.stage2 ops (NMX_R9_Children241.original choices) p accounts data slot =
 NMX_R8_Code241.body ops (NMX_R9_Children241.grouped choices) p accounts data slot := by
 rw [←NMX_R8_OldFactor241.source,←NMX_R8_Factor241.source]
 have continuation :
   NMX_R8_OldFactor241.afterValidate ops (NMX_R9_Children241.original choices) =
   NMX_R8_Factor241.afterValidate ops (NMX_R9_Children241.grouped choices) := by
  funext val accounts
  exact NMX_R9_After241.grouped choices ops val accounts
 unfold NMX_R8_OldFactor241.head NMX_R8_Factor241.head
 rw [continuation]
 rfl

#print axioms source
end NMX_R9_GroupHead241
end
