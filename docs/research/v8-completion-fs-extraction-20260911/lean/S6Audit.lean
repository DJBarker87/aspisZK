import S6GuardErasure
import S6DynamicGuardCut
import S6KilledKernelEnvelope
import S6FiniteEnvelope
import S6FirstCreatorList

/-! Aggregate only after each S6 leaf has compiled.  It asserts no selected
source refinement, cached-output result, payment extraction, or global FS
claim. -/

set_option autoImplicit false

#print axioms AspisS6.accepting_run_survives_erasure
#print axioms AspisS6.accepted_guarded_context
#print axioms AspisS6.accepted_guarded_is_relaxed
#print axioms AspisS6.KilledKernel.actual_le_ideal
#print axioms AspisS6.FiniteEnvelope.uniform_prefix_cap
#print axioms AspisS6.FirstCreator.first_append_when_present
