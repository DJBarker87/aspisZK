import R1Z.PV_Src_Consumer
import R1Z.PV_Src_Fixtures

/-! Final focused dependency-closure and axioms audit. Run once after the
individual changed modules and both fixture fibres compile. This is not a
shipped-execution or binary-association certificate. -/
#print R1Z.BuilderSource.SourceIdentification
#print R1Z.PV_Src_Identification.PV_Src_Premises
#print R1Z.PV_Src_Canonical.Instance
#print axioms R1Z.PV_Src_PartsTotal.parts_total
#print axioms R1Z.PV_Src_Public.run_success
#print axioms R1Z.PV_Src_Public.output_eq
#print axioms R1Z.PV_Src_Trace.run_exact
#print axioms R1Z.PV_Src_Trace.canonical_trace
#print axioms R1Z.PV_Src_Identification.public_eq
#print axioms R1Z.PV_Src_Identification.build_eq
#print axioms R1Z.PV_Src_Identification.transport_eq
#print axioms R1Z.PV_Src_Identification.identification
#print axioms R1Z.PV_Src_Canonical.premises
#print axioms R1Z.PV_Src_Canonical.identification
#print axioms R1Z.PV_Src_Canonical.public_eq
#print axioms R1Z.PV_Src_Canonical.build_eq
#print axioms R1Z.PV_Src_Canonical.transport_eq
#print axioms R1Z.PV_Src_Consumer.of_identification
#print axioms R1Z.PV_Src_Consumer.extracted_stages
#print axioms R1Z.PV_Src_Consumer.existing_consumer
#print axioms R1Z.PV_Src_Fixtures.fixture_run
#print axioms R1Z.PV_Src_Fixtures.fibres

#print R1Z.PV_Src_ForestIdentification.PV_Src_Premises
#print axioms R1Z.PV_Src_ForestPartsTotal.parts_total
#print axioms R1Z.PV_Src_ForestTrace.run_exact
#print axioms R1Z.PV_Src_ForestIdentification.identification
#print axioms R1Z.PV_Src_ForestCanonical.identification
#print axioms R1Z.PV_Src_ForestCanonical.public_eq
#print axioms R1Z.PV_Src_ForestCanonical.build_eq
#print axioms R1Z.PV_Src_ForestCanonical.transport_eq
#print axioms R1Z.PV_Src_Consumer.forest_stages
