import NNY_FinalCombined
import NOF_PowersAssociation
import NOF_CommonConverse
import NOF_Tx2Op11
import NOF_A2Field
set_option autoImplicit false
/-! Coherent combined import: run-6 combined, NNU combined, every accepted NNY
module (via NNY_FinalCombined) and every accepted NOF proof module. -/
#print axioms AspisR1.NOF_PowersAssociation.identify
#print axioms AspisR1.NOF_PowersAssociation.canonical_gamma
#print axioms AspisR1.NOF_PowersAssociation.canonical_early
#print axioms AspisR1.NOF_PowersAssociation.canonical_of_early
#print axioms AspisR1.NOF_PowersAssociation.decode_link
#print axioms AspisR1.NOF_PowersAssociation.source
#print axioms AspisR1.NOF_CommonConverse.source_run
#print axioms AspisR1.NOF_CommonConverse.tail_transport
#print axioms AspisR1.NOF_CommonConverse.common
#print axioms AspisR1.NOF_Tx2Op11.tx2Op11
#print axioms AspisR1.NOF_A2Field.sdk_at_slot
#print axioms AspisR1.NOF_A2Field.reserved_at
#print axioms AspisR1.NOF_A2Field.field
example : NNH_ExactRemainingTypes.tx2Op11 := AspisR1.NOF_Tx2Op11.tx2Op11
