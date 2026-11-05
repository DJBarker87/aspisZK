import NGL_ArrayEquality
import NGL_ReadonlyModel
set_option autoImplicit false
noncomputable section
namespace NGL_AuthGuards
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev Key := AdapterRw.solana_pubkey.Pubkey
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Master := AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
abbrev PE := AdapterRw.solana_program_error.ProgramError

theorem registry_pool_rejected (ops : AdapterRw.Ops) (verifier pool : Key)
    (masterAccount registry entry : Account) (master : Master) (slot : U64)
    (bytes expected : Array U8 32#usize)
    (keyReply : ops.op39 pool = ok bytes) (slotReply : ops.op45 = ok expected)
    (different : bytes ≠ expected) :
    AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry ops verifier pool
      masterAccount master registry entry slot = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  have comparison : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 bytes expected = ok true := by
    rw [NGL_ArrayEquality.ne_value]
    simp only [different,decide_false,Bool.not_false]
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  rw [keyReply]
  simp only [bind_tc_ok,slotReply,comparison,if_true]

theorem registry_flag_rejected (ops : AdapterRw.Ops) (verifier pool : Key)
    (masterAccount registry entry : Account) (master : Master) (slot : U64)
    (bytes : Array U8 32#usize) (mask : U8)
    (keyReply : ops.op39 pool = ok bytes) (slotReply : ops.op45 = ok bytes)
    (maskReply : ops.op13 = ok mask) (disabled : master.verifier_policy.flags &&& mask = 0#u8) :
    AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry ops verifier pool
      masterAccount master registry entry slot = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) := by
  have comparison : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8 bytes bytes = ok false := by
    rw [NGL_ArrayEquality.ne_value]
    simp only [decide_true,Bool.not_true]
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_invariant_release_registry
  rw [keyReply]
  simp only [bind_tc_ok,slotReply,comparison,Bool.false_eq_true,if_false,maskReply,lift,disabled,if_true]

theorem authenticate_count_rejected (ops : AdapterRw.Ops) (verifier pool : Key)
    (accounts : Slice Account) (lane : U8) (slot : U64)
    (wrong : Slice.len accounts ≠ 7#usize) :
    AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts ops verifier accounts pool lane slot =
      ok (.Err (if Slice.len accounts < 7#usize then AdapterRw.solana_program_error.ProgramError.NotEnoughAccountKeys else AdapterRw.solana_program_error.ProgramError.InvalidArgument)) := by
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  simp only [if_neg wrong]
  split <;> rfl

theorem validate_length_rejected (ops : AdapterRw.Ops) (verifier : Key)
    (accounts : Slice Account) (data : Slice U8) (slot : core.result.Result U64 PE)
    (size : Usize)
    (sizeReply : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES = ok size)
    (wrong : Slice.len data ≠ size) :
    AdapterRw.r1_pool_adapter.owned.validate_asq8 ops verifier accounts data slot =
      ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData) := by
  unfold AdapterRw.r1_pool_adapter.owned.validate_asq8
  rw [sizeReply]
  have mismatch : (Slice.len data != size) = true := by simp [wrong]
  simp only [bind_tc_ok,mismatch,if_true]
#print axioms registry_pool_rejected
#print axioms registry_flag_rejected
#print axioms authenticate_count_rejected
#print axioms validate_length_rejected
end NGL_AuthGuards
