-- Focused integration check only; no G0/top/manifest replay or export.
import NNH_ContinuationCombined
import NNH_S5FocusedHost
import NNM_COMBINED_IMPORT
import NNR_BinderHost
import NNQ_COMBINED_IMPORT2
import NNP_COMBINED_IMPORT
import NNO_StatementChecks
import NNH_DigestSyntaxTransport
import NNH_Run5bA1Domain
import NNH_Run5bAcceptance
import NNH_Run5bBinder
import NNH_Run5bClaims
import NNH_Run5bClock
import NNH_Run5bCtx
import NNH_Run5bCurrentExpand
import NNH_Run5bCurrentInitial
import NNH_Run5bCurrentPending
import NNH_Run5bCurrentShape
import NNH_Run5bCurrentValues
import NNH_Run5bCurrentView
import NNH_Run5bExec
import NNH_Run5bFinishEdge
import NNH_Run5bFullSpace
import NNH_Run5bGeometryMap
import NNH_Run5bGeometryReverse
import NNH_Run5bGeometrySlots
import NNH_Run5bGeometryUnits
import NNH_Run5bHeadline
import NNH_Run5bHeadlineB
import NNH_Run5bHost
import NNH_Run5bHostCharge
import NNH_Run5bIndexLaw
import NNH_Run5bNMF
import NNH_Run5bNMFRemaining
import NNH_Run5bPacket
import NNH_Run5bPreparedCore
import NNH_Run5bPreparedDigest
import NNH_Run5bPreparedModel
import NNH_Run5bPreparedSlot
import NNH_Run5bQueryDomain
import NNH_Run5bQuerySlots
import NNH_Run5bRecorderFixed
import NNH_Run5bRestClaims
import NNH_Run5bRestSetup
import NNH_Run5bReturnedGraph
import NNH_Run5bSplit

#print axioms AspisR1.NNH_DigestSyntaxTransport.account
#print axioms AspisR1.NNH_DigestSyntaxTransport.o1
#print axioms AspisR1.NNH_DigestSyntaxTransport.lower
#print axioms AspisR1.NNH_DigestSyntaxTransport.child
#print axioms AspisR1.NNH_DigestSyntaxTransport.first
#print axioms AspisR1.NNH_DigestSyntaxTransport.second
#print axioms AspisR1.NNH_Run5bA1Domain.returned
#print axioms AspisR1.NNH_Run5bAcceptance.a3
#print axioms AspisR1.NNH_Run5bAcceptance.a4
#print axioms AspisR1.NNH_Run5bAcceptance.a5
#print axioms AspisR1.NNH_Run5bBinder.host_shape
#print axioms AspisR1.NNH_Run5bBinder.exec_same
#print axioms AspisR1.NNH_Run5bBinder.top_splitB_grouped
#print axioms AspisR1.NNH_Run5bBinder.deployed_charge_grouped
#print axioms AspisR1.NNH_Run5bBinder.failG_eq
#print axioms AspisR1.NNH_Run5bBinder.indicator_eq_of_fixed
#print axioms AspisR1.NNH_Run5bBinder.indicator_eq_of_trust
#print axioms AspisR1.NNH_Run5bClaims.conclusion
#print axioms AspisR1.NNH_Run5bClock.environment
#print axioms AspisR1.NNH_Run5bClock.represented
#print axioms AspisR1.NNH_Run5bClock.no_disagreement
#print axioms AspisR1.NNH_Run5bClock.total_representation
#print axioms AspisR1.NNH_Run5bCtx.missing_at_slot
#print axioms AspisR1.NNH_Run5bCtx.env_unique
#print axioms AspisR1.NNH_Run5bCtx.selected_clock
#print axioms AspisR1.NNH_Run5bCtx.extraction
#print axioms AspisR1.NNH_Run5bCurrentExpand.semantic_slot
#print axioms AspisR1.NNH_Run5bCurrentExpand.semantic
#print axioms AspisR1.NNH_Run5bCurrentInitial.slot
#print axioms AspisR1.NNH_Run5bCurrentInitial.returned
#print axioms AspisR1.NNH_Run5bCurrentPending.source
#print axioms AspisR1.NNH_Run5bCurrentShape.slot
#print axioms AspisR1.NNH_Run5bCurrentShape.parse
#print axioms AspisR1.NNH_Run5bCurrentValues.slot
#print axioms AspisR1.NNH_Run5bCurrentView.slot
#print axioms AspisR1.NNH_Run5bCurrentView.returned
#print axioms AspisR1.NNH_Run5bExec.recSelect
#print axioms AspisR1.NNH_Run5bExec.environment_nonvacuous
#print axioms AspisR1.NNH_Run5bExec.recSig
#print axioms AspisR1.NNH_Run5bExec.exec
#print axioms AspisR1.NNH_Run5bFinishEdge.selected
#print axioms AspisR1.NNH_Run5bFullSpace.realizes
#print axioms AspisR1.NNH_Run5bFullSpace.same_event
#print axioms AspisR1.NNH_Run5bGeometryMap.closure
#print axioms AspisR1.NNH_Run5bGeometryMap.mapped
#print axioms AspisR1.NNH_Run5bGeometryMap.source
#print axioms AspisR1.NNH_Run5bGeometryReverse.step
#print axioms AspisR1.NNH_Run5bGeometryReverse.loop
#print axioms AspisR1.NNH_Run5bGeometryReverse.selected
#print axioms AspisR1.NNH_Run5bGeometrySlots.point
#print axioms AspisR1.NNH_Run5bGeometrySlots.line
#print axioms AspisR1.NNH_Run5bGeometrySlots.one
#print axioms AspisR1.NNH_Run5bGeometrySlots.subtract
#print axioms AspisR1.NNH_Run5bGeometrySlots.multiply
#print axioms AspisR1.NNH_Run5bGeometrySlots.double
#print axioms AspisR1.NNH_Run5bGeometrySlots.inverse
#print axioms AspisR1.NNH_Run5bGeometryUnits.canonical_one
#print axioms AspisR1.NNH_Run5bGeometryUnits.installed_one
#print axioms AspisR1.NNH_Run5bGeometryUnits.installed_inverse
#print axioms AspisR1.NNH_Run5bHeadline.headline
#print axioms AspisR1.NNH_Run5bHeadlineB.headlineB
#print axioms AspisR1.NNH_Run5bHost.account_at
#print axioms AspisR1.NNH_Run5bHost.S_host
#print axioms AspisR1.NNH_Run5bHost.a0
#print axioms AspisR1.NNH_Run5bHost.r0
#print axioms AspisR1.NNH_Run5bHostCharge.event_fixed
#print axioms AspisR1.NNH_Run5bHostCharge.bound
#print axioms AspisR1.NNH_Run5bIndexLaw.fibre_admitted
#print axioms AspisR1.NNH_Run5bIndexLaw.erase_index
#print axioms AspisR1.NNH_Run5bNMF.selected
#print axioms AspisR1.NNH_Run5bNMF.rootImage
#print axioms AspisR1.NNH_Run5bNMF.eventImage
#print axioms AspisR1.NNH_Run5bNMF.nmfB
#print axioms AspisR1.NNH_Run5bNMFRemaining.remaining
#print axioms AspisR1.NNH_Run5bPacket.cuts
#print axioms AspisR1.NNH_Run5bPacket.packet
#print axioms AspisR1.NNH_Run5bPreparedCore.installed
#print axioms AspisR1.NNH_Run5bPreparedDigest.digest
#print axioms AspisR1.NNH_Run5bPreparedModel.source
#print axioms AspisR1.NNH_Run5bPreparedSlot.fixed
#print axioms AspisR1.NNH_Run5bPreparedSlot.source
#print axioms AspisR1.NNH_Run5bQueryDomain.k
#print axioms AspisR1.NNH_Run5bQueryDomain.e
#print axioms AspisR1.NNH_Run5bQueryDomain.initial
#print axioms AspisR1.NNH_Run5bQuerySlots.decode
#print axioms AspisR1.NNH_Run5bQuerySlots.dots
#print axioms AspisR1.NNH_Run5bQuerySlots.circle
#print axioms AspisR1.NNH_Run5bQuerySlots.line
#print axioms AspisR1.NNH_Run5bQuerySlots.geometry
#print axioms AspisR1.NNH_Run5bQuerySlots.equality
#print axioms AspisR1.NNH_Run5bRecorderFixed.fixed
#print axioms AspisR1.NNH_Run5bRestClaims.Goal
#print axioms AspisR1.NNH_Run5bRestClaims.produce
#print axioms AspisR1.NNH_Run5bRestSetup.Goal
#print axioms AspisR1.NNH_Run5bRestSetup.produce
#print axioms AspisR1.NNH_Run5bReturnedGraph.ok
#print axioms AspisR1.NNH_Run5bReturnedGraph.not_ok
#print axioms AspisR1.NNH_Run5bSplit.conclusion_iff
#print axioms AspisR1.NNH_Run5bFullSpace.realizes
#print axioms AspisR1.NNH_Run5bFullSpace.same_event
#print axioms AspisR1.NNQ_HostDigest.o2
