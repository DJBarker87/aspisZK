import RPu_FIq_Terminal
import NDO_JFs_PublicSerialization
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_PublicSemantic
open Aeneas Aeneas.Std Result

def payment := FIq_Carriers.toTransfer (AspisR1PublicPreparation.PreparationBinding.fromTransfer JFs_PaymentValue.value)
def transition := FIq_Carriers.toTransition (AspisR1PublicPreparation.PreparationBinding.fromTransition JFs_LateChildren.value)
def pub : FIq_Carriers.NPublic := .Transfer payment transition

def value : FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic where
  variant := .PrivateTransfer
  pool := payment.pool
  deployment_domain := payment.deployment_domain
  anchor := payment.anchor_root
  nullifier := payment.nullifier
  asset_id := payment.asset_id
  recipient := some payment.recipient_commitment
  change := payment.change_commitment
  withdrawal_amount := none
  transition := transition

theorem public_eq : FIq_Carriers.toPublic JFs_PublicSerialization.value=pub := rfl

theorem source : FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic pub=ok value := rfl

#print axioms public_eq
#print axioms source
end AspisR1.JFu_PublicSemantic
end
