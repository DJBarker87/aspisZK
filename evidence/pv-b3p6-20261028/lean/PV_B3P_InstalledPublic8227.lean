import PV_B3P_Install227
import PV_B3P_PublicSuccess227
namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
noncomputable section

/-- Nonempty transfer family; arbitrary public digests remain symbolic. -/
def transfer_seed8 (p : reference_terminal.SemanticPublic) (recipient : Array U32 8#usize) :
    reference_terminal.SemanticPublic :=
  {p with variant := .PrivateTransfer, recipient := some recipient}

def installed_public8 (base : ProverRwFull.ExternalTypes)
    (p : reference_terminal.SemanticPublic) (recipient : Array U32 8#usize) :
    @ProverRwFull.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_B3P_Install227.Types base) :=
  letI : ProverRwFull.ExternalTypes := PV_B3P_Install227.Types base
  .Transfer
    (show PV_B3P_226V3.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 from
      ⟨p.pool, p.deployment_domain, 0#u64, p.anchor, p.nullifier,
        p.asset_id, recipient, p.change⟩)
    ⟨⟨p.pool, p.deployment_domain, 0#u64, 0#u64,
       p.transition.live_snapshot.current_root, empty_frontier⟩,
     (show aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 from
       ⟨1#u64, p.transition.candidate_afterstate.next_root, empty_frontier⟩)⟩

theorem installed_public_semantic8 (base : ProverRwFull.ExternalTypes)
    (p : reference_terminal.SemanticPublic) (recipient : Array U32 8#usize) :
    PV_B3P_Carrier227.semantic base (installed_public8 base p recipient) =
      valid_public (transfer_seed8 p recipient) := rfl

#print axioms installed_public_semantic8
end
end PV_B3P_Success227
