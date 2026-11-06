import AdapterRwScalar
import NLK_RegistryInstall
import NLK_LaneInstall
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace NLK_OwnedPrefixes
open Aeneas Aeneas.Std Result
abbrev Account := AdapterRw.r1_pool_adapter.owned.OwnedAccount
abbrev Key := AdapterRw.solana_pubkey.Pubkey
/-- Explicit partial local installation. Unreached children remain fail-closed.
These are rejection-prefix theorems, NEVER full233/242 invocation roots. -/
def ops (pda : NLK_RegistryInstall.Pda) (loader : Key) (devnet : Bool) :=
 {(NLK_RegistryInstall.ops pda loader devnet) with op50:=NLK_LaneProgram.reference}

theorem account_cardinality (pda : NLK_RegistryInstall.Pda) (loader : Key) (devnet : Bool)
 (verifier pool : Key) (accounts : Slice Account) (lane : U8) (slot : U64)
 (bad : accounts.len≠7#usize) :
 AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  (ops pda loader devnet) verifier accounts pool lane slot=
 (if accounts.len<7#usize then ok (.Err AdapterRw.solana_program_error.ProgramError.NotEnoughAccountKeys)
 else ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidArgument)) := by
 unfold AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
 simp only [if_neg bad]

theorem instruction_extent (pda : NLK_RegistryInstall.Pda) (loader : Key) (devnet : Bool)
 (verifier : Key) (accounts : Slice Account) (instruction : Slice U8)
 (slot : core.result.Result U64 AdapterRw.solana_program_error.ProgramError)
 (bad : instruction.len≠320#usize) :
 AdapterRw.r1_pool_adapter.owned.validate_asq8
  (ops pda loader devnet) verifier accounts instruction slot=
 ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData) := by
 unfold AdapterRw.r1_pool_adapter.owned.validate_asq8
 have size : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES=ok 320#usize := by
  unfold AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  unfold AdapterRw.aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  rw [AspisR1.AdapterRw.Scalar.mul_eq 3#usize 32#usize 96#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  rw [AspisR1.AdapterRw.Scalar.add_eq 8#usize 96#usize 104#usize (by scalar_tac)]
  simp only [bind_tc_ok]
  exact AspisR1.AdapterRw.Scalar.add_eq 104#usize 216#usize 320#usize (by scalar_tac)
 simp only [size,bind_tc_ok]
 simp [bad]
#print account_cardinality
#print axioms account_cardinality
#print instruction_extent
#print axioms instruction_extent
end NLK_OwnedPrefixes
