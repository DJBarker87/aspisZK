import NDM_CohortGate
import NDM_CohortConstructors
set_option autoImplicit false
namespace NDM_CohortReconstruction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct
open aspis_statement.pool_v1
abbrev Request := pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev Auth := r1_pool_adapter.AuthenticatedAsq8Accounts
abbrev Candidate := pair_terminal.PoolV1PairVerifiedAfterstateV1

def requested (request : Request) : U32 := match request.public with
 | .PrivateTransfer p=>p.asset_id
 | .Withdrawal p=>p.asset_id

def finish (request : Request) (a : Auth) (c : Candidate) := do
 let common ← r1_pool_adapter.asq8_common a c
 match request.public with
 | .PrivateTransfer p=>r1_pool_adapter.transfer_statement_box common p
 | .Withdrawal p=>r1_pool_adapter.withdrawal_statement_box common p

def direct (request : Request) (a : Auth) (c : Candidate) :=
 if a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val then
  if a.master.identity.asset_id=requested request then finish request a c
  else ok (core.result.Result.Err solana_program_error.ProgramError.InvalidInstructionData)
 else ok (core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData)

theorem word_cond {T : Type} (x y : U32) (a b : T) :
 (if x.val=y.val then a else b)=(if x=y then a else b) := by
 have eqv : x.val=y.val ↔ x=y := ⟨UScalar.eq_of_val_eq,congrArg (fun z : U32=>z.val)⟩
 rw [eqv]

/-- Actual emitted reconstruction control with actual emitted constructors,
 valid for every input. This is model-only; K082 gives no native gate credit. -/
theorem control (request : Request) (a : Auth) (c : Candidate) :
 r1_pool_adapter.reconstruct_asq8_statement request a c=direct request a c := by
 have gate := NDM_CohortGate.option_natural a.live_snapshot.next_pair_index c.next_pair_index
 simp only [lift,bind_tc_ok] at gate
 unfold r1_pool_adapter.reconstruct_asq8_statement
 simp only [lift,bind_tc_ok]
 rw [gate]
 simp only [bind_tc_ok]
 cases request with
 | mk profile release program payment=>
  cases payment <;>
   by_cases step : a.live_snapshot.next_pair_index.val+1=c.next_pair_index.val <;>
   simp [direct,finish,requested,step,NDM_CohortGate.field_reference] <;>
   exact word_cond _ _ _ _

#print axioms word_cond
#print axioms control
end NDM_CohortReconstruction
