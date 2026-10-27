-- Final additive callback/reference publication audit; no native closure inference.
import R1Z.PV_CBL_CallbackPublication
import R1Z.PV_CBL_ArraySliceBridge
import R1Z.PV_CBL_PopSliceCases
namespace R1Z.PV_CBL_CallbackBundle
abbrev array_reference_source := @PV_CBL_ArraySliceLaw.source
abbrev array_qm31_reference_source := PV_CBL_ArraySliceBridge.source
abbrev pop_empty_source := @PV_CBL_PopSliceCases.empty
abbrev pop_marker_irrelevant := @PV_CBL_PopSliceCases.marker_irrelevant
#print axioms array_reference_source
#print axioms array_qm31_reference_source
#print axioms pop_empty_source
#print axioms pop_marker_irrelevant
#print axioms op25_source_append
#print axioms op26_source
#print axioms op28_source_append
#print axioms op29_source_append
#print axioms op30_source_append
#print axioms op31_source_append
#print axioms op34_source_append
#print axioms op35_source_append
#print axioms soft_padding_source
#print axioms soft_compress_source
#print axioms soft_update_source
#print axioms soft_finalize_source
#print axioms soft_digest_source
end R1Z.PV_CBL_CallbackBundle
