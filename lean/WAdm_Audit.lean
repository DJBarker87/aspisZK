import Tx1Q_Accepted
import WAdm_NativeAccepted
import WAdm_NativeInstall
import WAdm_NativeInstance
import WAdm_FissionedRoot
import WAdm_FissionedFields
import WAdm_Nonvacuity
set_option pp.proofs false
set_option pp.maxDepth 256

#print axioms AspisR1.WAdm_NativeAccepted.accepted_pair_claims_tx1
#print axioms AspisR1.WAdm_NativeInstall.writer_slot
#print axioms AspisR1.WAdm_NativeInstall.other_slots
#print axioms AspisR1.WAdm_NativeInstall.on_run
#print axioms AspisR1.WAdm_NativeInstance.raw_body
#print axioms AspisR1.WAdm_NativeInstance.body_slice
#print axioms AspisR1.WAdm_NativeInstance.raw_accepted
#print axioms AspisR1.WAdm_NativeInstance.accepted
#print axioms AspisR1.WAdm_FissionedRoot.append
#print axioms AspisR1.WAdm_FissionedRoot.emitted
#print axioms AspisR1.WAdm_FissionedFields.returned
#print axioms AspisR1.WAdm_FissionedFields.body_bytes
#print axioms AspisR1.WAdm_Nonvacuity.domain_nonempty
#print axioms AspisR1.WAdm_Nonvacuity.extraction_satisfiable

#check @AspisR1.Tx1Q_Accepted.accepted_pair_claims_tx1
#check @AspisR1.WAdm_NativeAccepted.accepted_pair_claims_tx1
#print AspisR1.WAdm_Domain.SessionAPrepare
#print AspisR1.WAdm_Domain.Admitted
#print AspisR1.WAdm_Carrier.WideInputs
#print AspisR1.WAdm_NativeInstall.install
