import R1MaskedSemantic
import R1SamplerBytePass

/-! Combined import and axiom audit for the focused semantic/sampler reuse
checkpoint. The conclusions retain their explicit premises and model scope;
this is not an R1 Fiat--Shamir, source-refinement, or privacy theorem. -/

#print axioms AspisR1.MaskedSemantic.large_matching_extracts
#print axioms AspisR1.SemanticTransport.witness_point_claims
#print axioms AspisR1.SemanticTransport.witness_baseTyped
#print axioms AspisR1.SamplerBytePass.machineProcess_bytes_correct
#print axioms R0P.SemSource.semanticBad_card
#print axioms R0P.Mask.etaBad_semChal_mass
