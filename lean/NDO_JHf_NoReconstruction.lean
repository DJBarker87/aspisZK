import JHf_Carrier14
import NDO_JHf_RawStatementDomainGuard
import NDO_JHf_RequestDomain
import ExtractedAdapterReconstructSuccess
set_option autoImplicit false
namespace AspisR1.JHf_NoReconstruction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct r1_pool_adapter
open aspis_statement.pool_v1.pair_forest_terminal

def request := JHf_Carrier.toRequest JHd_RequestCarrier.actual

theorem source (a : AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (faithful : a.live_snapshot.deployment_domain=JHf_DomainBytes.master) :
    ¬∃ out,reconstruct_asq8_statement request a candidate=ok (.Ok out) := by
  rintro ⟨out,run⟩
  obtain ⟨_,_,same,valid⟩:=AdapterReconstructSuccess.reconstruct_success request a candidate out run
  have guard:=JHf_RawStatementDomainGuard.source out valid
  rw [same] at guard
  change core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JHf_RequestDomain.value a.live_snapshot.deployment_domain=ok false at guard
  rw [faithful,JHf_RequestDomain.compare] at guard
  cases guard
#print axioms source
end AspisR1.JHf_NoReconstruction
