import FIq_Carriers
import FIq_Native03
import TerminalSemanticPublicFieldsCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PublicCopy
open Aeneas Aeneas.Std Result
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
abbrev Public := FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic
/-- Pure carrier map of the existing checked public-preparation copy. -/
def native (p : SemanticPublic) : Public where
  variant := match p.variant with | .PrivateTransfer => .PrivateTransfer | .Withdrawal => .Withdrawal
  pool := p.pool
  deployment_domain := p.deployment_domain
  anchor := p.anchor
  nullifier := p.nullifier
  asset_id := p.asset_id
  recipient := p.recipient
  change := p.change
  withdrawal_amount := p.withdrawal_amount
  transition := {
    live_snapshot := {
      pool := p.transition.live_snapshot.pool
      deployment_domain := p.transition.live_snapshot.deployment_domain
      sequence := p.transition.live_snapshot.sequence
      next_pair_index := p.transition.live_snapshot.next_pair_index
      current_root := p.transition.live_snapshot.current_root
      frontier := p.transition.live_snapshot.frontier }
    candidate_afterstate := {
      next_pair_index := p.transition.candidate_afterstate.next_pair_index
      next_root := p.transition.candidate_afterstate.next_root
      next_frontier := p.transition.candidate_afterstate.next_frontier } }
/-- SAME installed constructor on the SAME statement; no separate public
witness or value equality hypothesis is supplied. -/
theorem on_statement (s : AspisR1TerminalDecoder.PublicBinding.Statement) :
    FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.semantic
      (FIq_Carriers.toPublic (AspisR1PublicPreparation.PreparationBinding.preparationPublic s))=
    ok (native (copyFromStatement s)) := by
  cases s <;> rfl
#print axioms on_statement
end AspisR1.FJa_PublicCopy
end
