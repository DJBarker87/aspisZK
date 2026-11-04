import Lean
import NFY_Part053

set_option autoImplicit false
noncomputable section
namespace NGE_NEL_PaymentDomains
open Aeneas Aeneas.Std Result NFY_NBG_PaymentChecks NFY_NBG_PaymentValidators

theorem common_accepted (c : C) (accepted : common c = .Ok ()) :
    zero c.pool = false ∧ zero c.deployment_domain = false ∧
    c.anchor_sequence.val ≤ 1048576 ∧ canonical c.anchor_root = true ∧
    canonical c.nullifier = true ∧ c.asset_id.val < 2147483647 := by
  unfold common at accepted
  repeat' split at accepted
  all_goals simp_all <;> omega

theorem transfer_accepted (p : T) (accepted : transfer p = .Ok ()) :
    common (tc p) = .Ok () ∧ canonical p.recipient_commitment = true ∧
      canonical p.change_commitment = true := by
  unfold transfer at accepted
  cases hc : common (tc p) with
  | Err e => simp only [hc,reduceCtorEq] at accepted
  | Ok u =>
    cases u
    simp only [hc] at accepted
    split at accepted
    · contradiction
    · simp_all

theorem withdrawal_accepted (p : W) (accepted : withdrawal p = .Ok ()) :
    common (wc p) = .Ok () ∧ 0 < p.amount.val ∧ p.amount.val < 1073741824 ∧
      zero p.destination_token_account = false ∧ canonical p.change_commitment = true := by
  unfold withdrawal at accepted
  cases hc : common (wc p) with
  | Err e => simp only [hc,reduceCtorEq] at accepted
  | Ok u =>
    cases u
    simp only [hc] at accepted
    repeat' split at accepted
    all_goals simp_all <;> omega

#print axioms common_accepted
#print axioms transfer_accepted
#print axioms withdrawal_accepted
end NGE_NEL_PaymentDomains

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
