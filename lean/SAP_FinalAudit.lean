import SAP_ActualCaller
import SAP_ActualCont
import SAP_ActualFull
import SAP_ActualPair
import SAP_ActualResult
import SAP_ActualTop
import SAP_AlphaTransport
import SAP_Attach
import SAP_Batches
import SAP_Binding
import SAP_BindingUnique
import SAP_CPhy
import SAP_CanonicalCarrier
import SAP_CircleCanonical
import SAP_Claims
import SAP_CloseConsumer
import SAP_ClosedCaller
import SAP_ClosedCont
import SAP_ClosedFull
import SAP_ClosedOutcome
import SAP_ClosedPair
import SAP_ClosedResult
import SAP_ClosedTop
import SAP_ConfigScope
import SAP_CoordinateTransport
import SAP_CurrentNumeric
import SAP_Cuts
import SAP_D189
import SAP_DataAssociation
import SAP_DataReadUnique
import SAP_DirectCaller
import SAP_DirectConsumer
import SAP_DirectCont
import SAP_DirectFull
import SAP_DirectOutcome
import SAP_DirectPair
import SAP_DirectResult
import SAP_DirectTop
import SAP_Discovery
import SAP_FieldsExact
import SAP_FinishConsumer
import SAP_FinishEffects
import SAP_FinishParsed
import SAP_FinishSaved
import SAP_FrozenSdk
import SAP_FrozenSource
import SAP_Immutable
import SAP_InputQuery
import SAP_InputUnique
import SAP_Install
import SAP_LiteralCaller
import SAP_LiteralConsumer
import SAP_LiteralCont
import SAP_LiteralFields
import SAP_LiteralFull
import SAP_LiteralOutcome
import SAP_LiteralPair
import SAP_LiteralResult
import SAP_LiteralTop
import SAP_NativePair
import SAP_Nonvacuity
import SAP_NumericFields
import SAP_NumericTransport
import SAP_Op3
import SAP_OpeningCuts
import SAP_OpeningShape
import SAP_PairSelected
import SAP_Physical
import SAP_PortUnique
import SAP_PrepareOwner
import SAP_PreparedFields
import SAP_Rebind
import SAP_ResultSelected
import SAP_SameDigest
import SAP_SampleCanonical
import SAP_SaveOnRun
import SAP_Scheduled
import SAP_SdkAccepted
import SAP_SdkUnion
import SAP_SemanticCanonical
import SAP_SemanticCircles
import SAP_SourceConsumer
import SAP_SourceOutcome
import SAP_Success
import SAP_TenSource
import SAP_Top
import SAP_Tx2
import SAP_Union
import SAP_WrapperCanonical
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
#check @AspisR1.T2R_Top.deployed
#check @AspisR1.SAP_Top.deployed
#check @AspisR1.SAP_LiteralTop.deployed
#check @AspisR1.SAP_DataAssociation.associate
#check @AspisR1.SAP_InputUnique.unique
#check @AspisR1.SAP_ConfigScope.exact_scope
#check @AspisR1.SAP_Nonvacuity.accepted_input
#print AspisR1.SAP_LiteralFull.Outcome
#print AspisR1.SAP_LiteralCaller.Outcome
#print AspisR1.SAP_LiteralCont.Outcome
#print AspisR1.SAP_LiteralOutcome.Outcome
#print AspisR1.SAP_LiteralFields.Fields
#print AspisR1.SAP_FinishSaved.Outcome
#print AspisR1.T2R_FullResult.Outcome
#print AspisR1.T2R_CallerSource.Outcome
#print AspisR1.T2R_ContSource.Outcome
#print AspisR1.T2R_Ten.Outcome
#print AspisR1.T2R_Finish.Outcome
#print AspisR1.SAP_CurrentNumeric.numeric
#print AspisR1.SAP_Install.configuration
#print AspisR1.DrvC_Installation.Configuration
#print AspisR1.WAdm_Domain.SessionAPrepare
#print AspisR1.Port5Q1_QueryPorts.SessionAPrepare
#print AspisR1.Port5Q2_Prepared.SessionAPrepare
#print AspisR1.Port5Q2_Prepared.PreparedFields
#print AspisR1.T2R_Acceptance.Facts
#print axioms AspisR1.SAP_ActualPair.accepted
#print axioms AspisR1.SAP_ActualTop.deployed
#print axioms AspisR1.SAP_AlphaTransport.alpha
#print axioms AspisR1.SAP_Attach.from_cut
#print axioms AspisR1.SAP_Batches.accepted_pair_claims_op5
#print axioms AspisR1.SAP_Binding.prepare
#print axioms AspisR1.SAP_BindingUnique.queries
#print axioms AspisR1.SAP_BindingUnique.data_fields
#print axioms AspisR1.SAP_BindingUnique.context
#print axioms AspisR1.SAP_CPhy.accepted_pair_unified
#print axioms AspisR1.SAP_CanonicalCarrier.wide
#print axioms AspisR1.SAP_CanonicalCarrier.qm
#print axioms AspisR1.SAP_CircleCanonical.source
#print axioms AspisR1.SAP_Claims.accepted_pair_claims
#print axioms AspisR1.SAP_CloseConsumer.close
#print axioms AspisR1.SAP_ClosedPair.accepted
#print axioms AspisR1.SAP_ClosedTop.deployed
#print axioms AspisR1.SAP_ConfigScope.dictionary_fields
#print axioms AspisR1.SAP_ConfigScope.install_idempotent
#print axioms AspisR1.SAP_ConfigScope.exact_scope
#print axioms AspisR1.SAP_CoordinateTransport.coordinates
#print axioms AspisR1.SAP_Cuts.buffers
#print axioms AspisR1.SAP_D189.accepted_run
#print axioms AspisR1.SAP_DataAssociation.associate
#print axioms AspisR1.SAP_DataReadUnique.unique
#print axioms AspisR1.SAP_DirectConsumer.direct
#print axioms AspisR1.SAP_DirectPair.accepted
#print axioms AspisR1.SAP_DirectTop.deployed
#print axioms AspisR1.SAP_Discovery.from_cut
#print axioms AspisR1.SAP_FieldsExact.numeric
#print axioms AspisR1.SAP_FieldsExact.iff_numeric
#print axioms AspisR1.SAP_FinishConsumer.consume
#print axioms AspisR1.SAP_FinishEffects.accepted_pair_unified
#print axioms AspisR1.SAP_FinishParsed.consume
#print axioms AspisR1.SAP_FinishSaved.consume
#print axioms AspisR1.SAP_FrozenSdk.accepted
#print axioms AspisR1.SAP_FrozenSource.accepted_pair
#print axioms AspisR1.SAP_Immutable.on_run
#print axioms AspisR1.SAP_InputQuery.decoded
#print axioms AspisR1.SAP_InputUnique.unique
#print axioms AspisR1.SAP_Install.circle
#print axioms AspisR1.SAP_Install.boundaries
#print axioms AspisR1.SAP_Install.unchanged_if_installed
#print axioms AspisR1.SAP_LiteralConsumer.literal
#print axioms AspisR1.SAP_LiteralFields.of_numeric
#print axioms AspisR1.SAP_LiteralPair.accepted
#print axioms AspisR1.SAP_LiteralTop.deployed
#print axioms AspisR1.SAP_NativePair.accepted_pair_unified
#print axioms AspisR1.SAP_Nonvacuity.accepted_input
#print axioms AspisR1.SAP_NumericFields.alpha
#print axioms AspisR1.SAP_NumericFields.semanticAlpha
#print axioms AspisR1.SAP_NumericFields.coordinate
#print axioms AspisR1.SAP_NumericTransport.numeric
#print axioms AspisR1.SAP_Op3.accepted_pair_claims_op3
#print axioms AspisR1.SAP_OpeningCuts.opening
#print axioms AspisR1.SAP_OpeningShape.fields
#print axioms AspisR1.SAP_PairSelected.accepted
#print axioms AspisR1.SAP_Physical.accepted_pair_unified
#print axioms AspisR1.SAP_PortUnique.rho
#print axioms AspisR1.SAP_PortUnique.queries
#print axioms AspisR1.SAP_PortUnique.no_all_rho
#print axioms AspisR1.SAP_PrepareOwner.installed
#print axioms AspisR1.SAP_PreparedFields.fields
#print axioms AspisR1.SAP_Rebind.prepared
#print axioms AspisR1.SAP_SameDigest.digest
#print axioms AspisR1.SAP_SampleCanonical.sample
#print axioms AspisR1.SAP_SampleCanonical.call
#print axioms AspisR1.SAP_SampleCanonical.calls
#print axioms AspisR1.SAP_SaveOnRun.saved
#print axioms AspisR1.SAP_Scheduled.accepted_run
#print axioms AspisR1.SAP_SdkAccepted.accepted_pair_unified
#print axioms AspisR1.SAP_SdkUnion.accepted_pair_unified
#print axioms AspisR1.SAP_SemanticCanonical.alpha
#print axioms AspisR1.SAP_SemanticCircles.coordinates
#print axioms AspisR1.SAP_SourceConsumer.from_cut
#print axioms AspisR1.SAP_Success.accepted_pair_claims_op5
#print axioms AspisR1.SAP_TenSource.from_cut
#print axioms AspisR1.SAP_Top.deployed
#print axioms AspisR1.SAP_Tx2.accepted_pair_claims_tx2
#print axioms AspisR1.SAP_Union.accepted_pair_unified
#print axioms AspisR1.SAP_WrapperCanonical.fallback_adapter_coordinates_canonical
#print axioms AspisR1.SAP_WrapperCanonical.successful_wrapper_circle_coordinates_canonical
