import XRo_Join_Carriers
import XRo_Join_DivPass
import XRo_Join_Installed
import XRo_Join_Nonvacuity
import XRo_Join_OrdinaryDecode
import XRo_Join_OrdinaryDigits
import XRo_Join_PowersAssociation
import XRo_Join_PowersLoop
import XRo_Join_PreparedAssociation
import XRo_Join_PreparedBoundaries
import XRo_Join_PreparedCuts
import XRo_Join_PreparedScalars
import XRo_Join_QmSampler
import XRo_Join_ResultPair
import XRo_Join_ResultTransport
import XRo_Join_Transcript
import XRo_Join_TranscriptBlock
import XRo_Join_TranscriptState

#print axioms XRo_Join_Carriers.cq_eq
#print axioms XRo_Join_Carriers.eq_cq
#print axioms XRo_Join_Carriers.cv_ev
#print axioms XRo_Join_Carriers.ev_cv
#print axioms XRo_Join_Carriers.cp_ep
#print axioms XRo_Join_Carriers.ep_cp
#print axioms XRo_Join_Carriers.arr_inverse
#print axioms XRo_Join_Carriers.cc_ec
#print axioms XRo_Join_Carriers.ec_cc
#print axioms XRo_Join_Carriers.cst_est
#print axioms XRo_Join_Carriers.est_cst
#print axioms XRo_Join_Carriers.ct_et
#print axioms XRo_Join_Carriers.et_ct
#print axioms XRo_Join_Carriers.cs_es
#print axioms XRo_Join_Carriers.es_cs
#print axioms XRo_Join_Carriers.cview_eview
#print axioms XRo_Join_Carriers.eview_cview
#print axioms XRo_Join_Carriers.cprepared_eprepared
#print axioms XRo_Join_Carriers.eprepared_cprepared
#print axioms XRo_Join_Carriers.cd_ed
#print axioms XRo_Join_Carriers.ed_cd
#print axioms XRo_Join_Carriers.ce_ee
#print axioms XRo_Join_Carriers.ee_ce
#print axioms XRo_Join_Carriers.mapR_bind
#print axioms XRo_Join_Carriers.nested_roundtrip
#print axioms XRo_Join_DivPass.pass
#print axioms XRo_Join_Installed.powers_slot
#print axioms XRo_Join_Installed.cached_claim_slot
#print axioms XRo_Join_Installed.serializer_slot
#print axioms XRo_Join_Installed.start
#print axioms XRo_Join_Installed.legacy_claim_unused
#print axioms XRo_Join_Nonvacuity.rejected_initialization
#print axioms XRo_Join_OrdinaryDecode.canonical
#print axioms XRo_Join_OrdinaryDecode.wide_new
#print axioms XRo_Join_OrdinaryDecode.decode
#print axioms XRo_Join_OrdinaryDecode.ordinary_slot
#print axioms XRo_Join_OrdinaryDigits.div_body
#print axioms XRo_Join_OrdinaryDigits.div_loop
#print axioms XRo_Join_PowersAssociation.powers
#print axioms XRo_Join_PowersLoop.suffix
#print axioms XRo_Join_PreparedAssociation.same_run
#print axioms XRo_Join_PreparedBoundaries.legacy_claim_unused
#print axioms XRo_Join_PreparedCuts.source
#print axioms XRo_Join_PreparedScalars.scalar
#print axioms XRo_Join_PreparedScalars.scalar_k
#print axioms XRo_Join_QmSampler.div_body
#print axioms XRo_Join_QmSampler.div_loop
#print axioms XRo_Join_QmSampler.div_pass
#print axioms XRo_Join_QmSampler.digits0_body
#print axioms XRo_Join_QmSampler.digits0
#print axioms XRo_Join_QmSampler.digits1_body
#print axioms XRo_Join_QmSampler.digits1
#print axioms XRo_Join_QmSampler.digits
#print axioms XRo_Join_QmSampler.sample
#print axioms XRo_Join_ResultPair.map_let_pair
#print axioms XRo_Join_ResultTransport.map_ok
#print axioms XRo_Join_ResultTransport.map_fail
#print axioms XRo_Join_ResultTransport.map_div
#print axioms XRo_Join_ResultTransport.map_if
#print axioms XRo_Join_ResultTransport.map_pair
#print axioms XRo_Join_ResultTransport.map_flow
#print axioms XRo_Join_ResultTransport.map_inner
#print axioms XRo_Join_ResultTransport.map_comp
#print axioms XRo_Join_ResultTransport.bind_map
#print axioms XRo_Join_ResultTransport.map_id
#print axioms XRo_Join_ResultTransport.map_injective
#print axioms XRo_Join_Transcript.tag
#print axioms XRo_Join_Transcript.folds
#print axioms XRo_Join_Transcript.start
#print axioms XRo_Join_TranscriptBlock.absorb
#print axioms XRo_Join_TranscriptBlock.block
#print axioms XRo_Join_TranscriptState.state
