import NGJ_VERIFIER_IMPORT
set_option autoImplicit false
namespace NIS_OwnedHeaders
open Aeneas Aeneas.Std Result AdapterRw
abbrev Account := r1_pool_adapter.owned.OwnedAccount

/-- Preserve both ordered byte-comparison calls, including their fail/div
prefixes, before the first owned stage rejects an incorrect account count. -/
theorem first_count (ops : AdapterRw.Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8) (wrong : accounts.val.length≠3) :
    r1_pool_adapter.owned.stage1_owned ops program accounts data = (do
      let ten ← ops.op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,10#u8])
      if ten then ok (.Err solana_program_error.ProgramError.InvalidInstructionData)
      else do
        let _ ← ops.op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,11#u8])
        ok (.Err solana_program_error.ProgramError.InvalidInstructionData)) := by
  have different : Slice.len accounts≠3#usize := by
    intro same
    exact wrong (congrArg UScalar.val same)
  have guard : (Slice.len accounts != 3#usize)=true := by simp [different]
  simp only [r1_pool_adapter.owned.stage1_owned,guard,ite_true,ite_self]

/-- A cut after the two actual comparisons. These are named child replies,
not an assumed parent acceptance; this lemma does not manufacture their laws. -/
theorem first_data (ops : AdapterRw.Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8)
    (ten : ops.op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,10#u8])=ok false)
    (eleven : ops.op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,11#u8])=ok false) :
    r1_pool_adapter.owned.stage1_owned ops program accounts data =
      ok (.Err solana_program_error.ProgramError.InvalidInstructionData) := by
  simp [r1_pool_adapter.owned.stage1_owned,ten,eleven]

/-- Stage2 rejects the count before any magic read, decoder, clock or child. -/
theorem second_count (ops : AdapterRw.Ops) (program : solana_pubkey.Pubkey)
    (accounts : Slice Account) (data : Slice U8)
    (slot : core.result.Result U64 solana_program_error.ProgramError)
    (wrong : accounts.val.length≠7) :
    r1_pool_adapter.owned.stage2_owned ops program accounts data slot =
      ok (.Err solana_program_error.ProgramError.InvalidInstructionData) := by
  have different : Slice.len accounts≠7#usize := by
    intro same
    exact wrong (congrArg UScalar.val same)
  have guard : (Slice.len accounts != 7#usize)=true := by simp [different]
  simp only [r1_pool_adapter.owned.stage2_owned,guard,ite_true]

#print axioms first_count
#print axioms first_data
#print axioms second_count
end NIS_OwnedHeaders
