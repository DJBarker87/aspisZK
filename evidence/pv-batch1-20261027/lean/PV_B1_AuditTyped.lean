import PV_B1_SelectedContract
import PV_B1_ReferenceInstall
import PV_B1_HostSumSource
import PV_B1_HostPoleTruth
import PV_B1_CarrierResultRecovery
import PV_B1_HostFailureIndependence
open Aeneas Aeneas.Std
-- Frozen dependency closure and standard-axiom audit only.
#print axioms PV_B1_SelectedContract.source_contract
#print axioms PV_B1_ReferenceInstall.source_eq
#print axioms PV_B1_ReferenceInstall.context_result
#print axioms PV_B1_HostSumSource.original_transport
#print axioms PV_B1_HostSumSource.op230_source
#print axioms PV_B1_HostPoleTruth.truth
#print axioms PV_B1_HostPoleTruth.falsity
#print axioms PV_B1_CarrierResultRecovery.wide
#print axioms PV_B1_CarrierResultRecovery.sum
#print axioms PV_B1_HostFailureIndependence.same_length
