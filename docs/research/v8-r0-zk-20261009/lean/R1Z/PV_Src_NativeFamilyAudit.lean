import R1Z.PV_Src_RecordRangeObstruction
import R1Z.PV_Src_RecordReference
import R1Z.PV_Src_NativeConsumer
import R1Z.PV_Src_Fixtures

/-! Focused audit of the unchanged five-field native contract, reference
candidate and unchanged consumer. No native fixture or deployment claim. -/
#print R1Z.PV_Src_NativeIdentification.PV_Src_Premises
#check @R1Z.PV_Src_NativeIdentification.PV_Src_Premises.compile_call
#check @R1Z.PV_Src_NativeIdentification.PV_Src_Premises.words
#check @R1Z.PV_Src_NativeIdentification.PV_Src_Premises.publicCorr
#check @R1Z.PV_Src_NativeIdentification.PV_Src_Premises.admission
#check @R1Z.PV_Src_NativeIdentification.PV_Src_Premises.row_call
#print R0Z.WriterRefine.WitnessOk
#print R0Z.WriterRefine.PubCorr
#print R1Z.PV_Src_RecordReference.Checked
#print axioms R1Z.PV_Src_RecordRangeObstruction.output_bound_required
#print axioms R1Z.PV_Src_RecordRangeObstruction.reference_counterexample
#print axioms R1Z.PV_Src_RecordReference.word_witness
#print axioms R1Z.PV_Src_RecordReference.word_public
#print axioms R1Z.PV_Src_RecordReference.newRecords_eq
#print axioms R1Z.PV_Src_RecordReference.words
#check @R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises
#print axioms R1Z.PrivacyR1HeadlineOwnedClosed.Admitted.builder_premises
#print axioms R1Z.PV_Src_NativeConsumer.builder_premises
#print axioms R1Z.PV_Src_NativeConsumer.phased_builder_premises
#print axioms R1Z.PV_Src_Fixtures.fixture_run
#print axioms R1Z.PV_Src_Fixtures.transfer_public
#print axioms R1Z.PV_Src_Fixtures.withdrawal_public
#print axioms R1Z.PV_Src_Fixtures.fibres
