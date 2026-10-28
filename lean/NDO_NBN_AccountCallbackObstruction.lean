import NDO_NBN_CallbackObstruction
set_option autoImplicit false
namespace NBN_AccountCallbackObstruction
open Aeneas Aeneas.Std Result
open AspisR1
abbrev PE := AdapterRw.solana_program_error.ProgramError

theorem master_unconstrained {F E : Type} (c : DrvC_Installation.Configuration F E)
    (input : Slice U8)
    (m : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) :
    ∃ reject accept : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk reject).op48 input = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) ∧
      (DrvC_Installation.sdk accept).op48 input = ok (.Ok m) := by
  exact ⟨{c with adapter := {c.adapter with op48 := fun _ => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)}},
    {c with adapter := {c.adapter with op48 := fun _ => ok (.Ok m)}},rfl,rfl⟩

theorem checkpoint_unconstrained {F E : Type} (c : DrvC_Installation.Configuration F E)
    (input : Slice U8)
    (m : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) :
    ∃ reject accept : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk reject).op49 input = ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) ∧
      (DrvC_Installation.sdk accept).op49 input = ok (.Ok m) := by
  exact ⟨{c with adapter := {c.adapter with op49 := fun _ => ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData)}},
    {c with adapter := {c.adapter with op49 := fun _ => ok (.Ok m)}},rfl,rfl⟩

theorem request_unconstrained {F E : Type} (c : DrvC_Installation.Configuration F E)
    (input : Slice U8)
    (m : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1) :
    ∃ reject accept : DrvC_Installation.Configuration F E,
      (DrvC_Installation.sdk reject).op23 input =
        ok (.Err .WrongLength) ∧
      (DrvC_Installation.sdk accept).op23 input = ok (.Ok m) := by
  exact ⟨{c with adapter := {c.adapter with op23 := fun _ => ok (.Err .WrongLength)}},
    {c with adapter := {c.adapter with op23 := fun _ => ok (.Ok m)}},rfl,rfl⟩

#print axioms master_unconstrained
#print axioms checkpoint_unconstrained
#print axioms request_unconstrained
end NBN_AccountCallbackObstruction
