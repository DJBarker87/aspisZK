import RPu_FIq_Carriers
import RPu_FIq_Native03
import RPv_PreparationPublicFieldsCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PublicCopy
open Aeneas Aeneas.Std Result
abbrev Public := FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic
/-- Pure value of the ORIGINAL installed semantic-public constructor. -/
def native : FIq_Carriers.Public → Public
  | .Transfer p t => {
      variant := .PrivateTransfer
      pool := p.pool
      deployment_domain := p.deployment_domain
      anchor := p.anchor_root
      nullifier := p.nullifier
      asset_id := p.asset_id
      recipient := some p.recipient_commitment
      change := p.change_commitment
      withdrawal_amount := none
      transition := FIq_Carriers.toTransition t }
  | .Withdrawal p t => {
      variant := .Withdrawal
      pool := p.pool
      deployment_domain := p.deployment_domain
      anchor := p.anchor_root
      nullifier := p.nullifier
      asset_id := p.asset_id
      recipient := none
      change := p.change_commitment
      withdrawal_amount := some p.amount
      transition := FIq_Carriers.toTransition t }
/-- SAME installed constructor; no separate semantic public witness. -/
theorem on_statement (p : FIq_Carriers.Public) :
    FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
      (FIq_Carriers.toPublic p)=ok (native p) := by
  cases p <;> rfl
#print axioms on_statement
end AspisR1.FJa_PublicCopy
end
