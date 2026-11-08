import NMX_R6_Nonempty
import NMX_R5_Native242
set_option autoImplicit false
noncomputable section
namespace NMX_R6_NativeLive242
open Aeneas Aeneas.Std Result AdapterRw NMX_R6_Nonempty

theorem live (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Live (NMS_R2N_Native242Children.meaning false (NMX_R4_NMS233.typed choices) program accounts data slot) := by
 unfold NMS_R2N_Native242Children.meaning NMS_R2N_242Code.body NMS_R2N_Native242Children.children
 repeat' first
 | exact NMX_R6_Nonempty.lift _
 | exact NMX_R6_Nonempty.pure _
 | exact NMX_R6_Nonempty.auth _ _ _ _ _ _
 | exact NMX_R6_Nonempty.getter _
 | exact NMX_R6_Nonempty.scan _
 | exact NMX_R6_Nonempty.reconstruct _ _ _
 | apply NMX_R6_Nonempty.bind
 | split
 | intro value

/-- Selects from the literal interpreted source, never from the target Ref.
All nondeterminism is the retained std allocation interpretation. -/
def observation (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) (env : RSL.Env) :=
 Classical.choose (live choices program accounts data slot env)

theorem source_member (choices : NMX_R4_Authentication.Choices)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) (env : RSL.Env) :
 NMS_R2N_Native242Children.meaning false (NMX_R4_NMS233.typed choices) program accounts data slot env
  (observation choices program accounts data slot env) :=
 Classical.choose_spec (live choices program accounts data slot env)

#print axioms live
#print axioms source_member
end NMX_R6_NativeLive242
end
