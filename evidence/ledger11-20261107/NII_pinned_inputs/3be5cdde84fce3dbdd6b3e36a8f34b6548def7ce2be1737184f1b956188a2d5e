import NHD_RequestSize
set_option autoImplicit false
noncomputable section
namespace NHD_ValidateLength
open Aeneas Aeneas.Std Result

theorem rejected (ops : AdapterRw.Ops) (verifier : NGL_AuthGuards.Key)
    (accounts : Slice NGL_AuthGuards.Account) (data : Slice U8)
    (slot : core.result.Result U64 NGL_AuthGuards.PE)
    (wrong : Slice.len data ≠ 320#usize) :
    AdapterRw.r1_pool_adapter.owned.validate_asq8 ops verifier accounts data slot =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData) := by
  exact NGL_AuthGuards.validate_length_rejected ops verifier accounts data slot
    320#usize NHD_RequestSize.request_size wrong
#print axioms rejected
end NHD_ValidateLength
