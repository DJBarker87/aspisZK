import SourceSqueeze
import SameBodyAssembly
import FSBoundedTranscript
import FSExposureOrder

/- This root checks the new source-shaped prerequisites ONLY. It deliberately
does not export SuccessfulAt, payment extraction, or a global probability. -/
#check @AspisV8Completion.SameBodyAssembly.preserves_semantic
#check @AspisV8Completion.SameBodyAssembly.preserves_ordinary
#check @AspisV8Completion.SameBodyRelation.produced_consumes
#check @AspisV8Completion.FSBoundedTranscript.constructed_cuts
#print axioms AspisV8Completion.SameBodyAssembly.preserves_semantic
#print axioms AspisV8Completion.SameBodyAssembly.preserves_ordinary
#print axioms AspisV8Completion.SameBodyRelation.produced_consumes
#print axioms AspisV8Completion.FSBoundedTranscript.constructed_cuts
#print axioms AspisV8Completion.FSBoundedTranscript.constructed_abort_prefix
#check @AspisV8Completion.FSExposureOrder.linked_order_or_premature_target
#print axioms AspisV8Completion.FSExposureOrder.linked_order_or_premature_target
#print axioms AspisV8Completion.FSExposureOrder.first_recorded_answer
