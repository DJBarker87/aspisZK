import NKI_InitialPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_TermPublic
open Aeneas Aeneas.Std Result FIq_Native
open pool_v1.pair_forest_semantic_terminal
/-- CLOSED255's exact frozen field transcription on the FIq emitted carrier.
The canonical model types are retained; no copied owner/type is introduced.
NHG_Semantic's preparation-carrier packet remains its native provenance. -/
def value : r0.Public → SemanticPublic
 | .Transfer p t =>
   {variant:=.PrivateTransfer,pool:=p.pool,deployment_domain:=p.deployment_domain,
    anchor:=p.anchor_root,nullifier:=p.nullifier,asset_id:=p.asset_id,
    recipient:=some p.recipient_commitment,change:=p.change_commitment,
    withdrawal_amount:=none,transition:=t}
 | .Withdrawal p t =>
   {variant:=.Withdrawal,pool:=p.pool,deployment_domain:=p.deployment_domain,
    anchor:=p.anchor_root,nullifier:=p.nullifier,asset_id:=p.asset_id,
    recipient:=none,change:=p.change_commitment,
    withdrawal_amount:=some p.amount,transition:=t}

theorem source (pub : r0.Public) : pub.semantic=ok (value pub) := by
 cases pub <;> rfl
#print source
#print axioms source
end AspisR1.NKR_TermPublic
end
