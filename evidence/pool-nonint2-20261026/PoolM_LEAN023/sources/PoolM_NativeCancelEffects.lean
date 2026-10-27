import PoolM_NativeCancelReject
set_option autoImplicit false
namespace AspisR1.PoolM_NativeCancelEffects
open Aeneas Aeneas.Std Result
open PoolM_NativeCancelSource PoolM_NativeCancelReject
abbrev Error := AdapterRw.solana_program_error.ProgramError
abbrev Account := AdapterRw.Cuts.Account
abbrev Key := AdapterRw.solana_pubkey.Pubkey

/-- An explicit cut carries its same state and complete ordered prior effects,
including on interpreter failure/divergence. It does not construct a native
whole-handler execution or assume any prefix had no effects. -/
structure Outcome (S E V : Type) where
  result : Result (core.result.Result V Error)
  state : S
  effects : List E

def afterGuard {S E V : Type} (guard : Result (core.result.Result Unit Error))
    (state : S) (prior : List E) (next : S → List E → Outcome S E V) : Outcome S E V :=
  match guard with
  | .ok (.Ok _) => next state prior
  | .ok (.Err e) => ⟨ok (.Err e),state,prior⟩
  | .fail e => ⟨fail e,state,prior⟩
  | .div => ⟨div,state,prior⟩

theorem exact_error {S E V : Type} (err : Error) (state : S) (prior : List E)
    (next : S → List E → Outcome S E V) :
    afterGuard (ok (.Err err)) state prior next = ⟨ok (.Err err),state,prior⟩ := rfl

theorem exact_failure {S E V : Type} (err : Std.Error) (state : S) (prior : List E)
    (next : S → List E → Outcome S E V) :
    afterGuard (fail err) state prior next = ⟨fail err,state,prior⟩ := rfl

theorem exact_divergence {S E V : Type} (state : S) (prior : List E)
    (next : S → List E → Outcome S E V) :
    afterGuard div state prior next = ⟨div,state,prior⟩ := rfl

/-- Rejected cuts retain every prior effect in order and their supplied state.
No close/refund/realloc/reassign/CPI operation in the suffix is run. -/
theorem blocked_frame {S E V : Type} (guard : Result (core.result.Result Unit Error))
    (blocked : guard ≠ ok (.Ok ())) (state : S) (prior : List E)
    (next : S → List E → Outcome S E V) :
    (afterGuard guard state prior next).state = state ∧
      (afterGuard guard state prior next).effects = prior := by
  cases guard with
  | ok r => cases r with
    | Ok u => cases u; exact False.elim (blocked rfl)
    | Err e => exact ⟨rfl,rfl⟩
  | fail e => exact ⟨rfl,rfl⟩
  | div => exact ⟨rfl,rfl⟩

theorem blocked_suffix {S E V : Type} (guard : Result (core.result.Result Unit Error))
    (blocked : guard ≠ ok (.Ok ())) (state : S) (prior : List E)
    (first second : S → List E → Outcome S E V) :
    afterGuard guard state prior first = afterGuard guard state prior second := by
  cases guard with
  | ok r => cases r with
    | Ok u => cases u; exact False.elim (blocked rfl)
    | Err e => rfl
  | fail e => rfl
  | div => rfl

/-- Native extracted ASPX core-role exclusion now composes with any suffix,
without an assumed accepted child or empty earlier-effect list. -/
theorem core_no_suffix {S E V : Type} (readLength : Account → Result Usize)
    (system id : Key) (payer coreAcc shard : Account) (hasShard : Bool) (n : Usize)
    (cp : n.val = 192 ∨ n.val = 1768) (actual : readLength coreAcc = ok n)
    (state : S) (prior : List E) (first second : S → List E → Outcome S E V) :
    afterGuard (PoolM_cancel_roles_native readLength system id payer coreAcc shard hasShard)
        state prior first =
      afterGuard (PoolM_cancel_roles_native readLength system id payer coreAcc shard hasShard)
        state prior second :=
  blocked_suffix _ (core_occupied readLength system id payer coreAcc shard hasShard n cp actual)
    state prior first second

theorem shard_no_suffix {S E V : Type} (readLength : Account → Result Usize)
    (system id : Key) (payer coreAcc shard : Account) (n : Usize)
    (cp : n.val = 192 ∨ n.val = 1768) (actual : readLength shard = ok n)
    (state : S) (prior : List E) (first second : S → List E → Outcome S E V) :
    afterGuard (PoolM_cancel_roles_native readLength system id payer coreAcc shard true)
        state prior first =
      afterGuard (PoolM_cancel_roles_native readLength system id payer coreAcc shard true)
        state prior second :=
  blocked_suffix _ (shard_occupied readLength system id payer coreAcc shard n cp actual)
    state prior first second

#print axioms exact_error
#print axioms exact_failure
#print axioms exact_divergence
#print axioms blocked_frame
#print axioms blocked_suffix
#print axioms core_no_suffix
#print axioms shard_no_suffix
end AspisR1.PoolM_NativeCancelEffects
