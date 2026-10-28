import JHf_Carrier6
import NDO_JHf_ReconstructDomain
import NDO_JGx_RealStatement
set_option autoImplicit false
namespace AspisR1.JHf_ExactDomainObstruction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct r1_pool_adapter
open aspis_statement.pool_v1.pair_forest_terminal

theorem target_domain :
    JHf_ReconstructDomain.domain (JHf_Carrier.toPoolV1PairForestTerminalStatementV1 JGx_RealStatement.value)=
      JFt_SnapshotValue.value.deployment_domain := rfl
#print axioms target_domain

theorem cannot_reconstruct (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (faithful : a.live_snapshot.deployment_domain=JHf_DomainBytes.master) :
    reconstruct_asq8_statement request a candidate≠
      ok (.Ok (JHf_Carrier.toPoolV1PairForestTerminalStatementV1 JGx_RealStatement.value)) :=
  JHf_ReconstructDomain.cannot_match request a candidate _ faithful target_domain
#print axioms cannot_reconstruct
end AspisR1.JHf_ExactDomainObstruction
