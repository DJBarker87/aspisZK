import Lean
import NGE_NEL_PaymentDomains

set_option autoImplicit false
noncomputable section
namespace NGE_NEL_PaymentOracle
open Aeneas Aeneas.Std Result NFY_NBG_PaymentChecks NFY_NBG_PaymentValidators
abbrev Reply := core.result.Result Unit E

def transfer_value (reply : Reply) (recipient change : Bool) : Reply :=
  match reply with
  | .Err e => .Err e
  | .Ok () => if !recipient || !change then .Err .NonCanonicalDigest else .Ok ()

def withdrawal_value (p : W) (reply : Reply) (change : Bool) : Reply :=
  match reply with
  | .Err e => .Err e
  | .Ok () => if p.amount.val = 0 ∨ p.amount.val >= 1073741824 then .Err .InvalidWithdrawalAmount
      else if zero p.destination_token_account then .Err .InvalidDestination
      else if !change then .Err .NonCanonicalDigest else .Ok ()

theorem transfer_substitution (p : T) :
    transfer_value (common (tc p)) (canonical p.recipient_commitment)
      (canonical p.change_commitment) = transfer p := by rfl

theorem withdrawal_substitution (p : W) :
    withdrawal_value p (common (wc p)) (canonical p.change_commitment) = withdrawal p := by rfl

def transfer_calls (reply : Reply) (recipient : Bool) : List Nat :=
  match reply with
  | .Err _ => [0]
  | .Ok () => if !recipient then [0,1] else [0,1,2]

def withdrawal_calls (p : W) (reply : Reply) : List Nat :=
  match reply with
  | .Err _ => [0]
  | .Ok () => if p.amount.val = 0 ∨ p.amount.val >= 1073741824 then [0]
      else if zero p.destination_token_account then [0] else [0,1]

theorem transfer_call_count (reply : Reply) (recipient : Bool) :
    (transfer_calls reply recipient).length =
      match reply with | .Err _ => 1 | .Ok () => if !recipient then 2 else 3 := by
  cases reply with
  | Err e => rfl
  | Ok u => cases u; cases recipient <;> rfl

theorem withdrawal_call_count (p : W) (reply : Reply) :
    (withdrawal_calls p reply).length =
      (match reply with
       | .Err _ => 1
       | .Ok () =>
         if p.amount.val = 0 ∨ p.amount.val >= 1073741824 then 1
         else if zero p.destination_token_account then 1 else 2) := by
  cases reply with
  | Err e => rfl
  | Ok u =>
    cases u
    by_cases bad : p.amount.val = 0 ∨ p.amount.val >= 1073741824 <;>
      by_cases dest : zero p.destination_token_account = true <;>
        simp [withdrawal_calls,bad,dest]

#print axioms transfer_substitution
#print axioms withdrawal_substitution
#print axioms transfer_call_count
#print axioms withdrawal_call_count
end NGE_NEL_PaymentOracle

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
