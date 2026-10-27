import R1Z.PV_RunJoin_ReferenceReturned
import R1Z.PV_RunJoin_FixtureAdmission

/-! Admission of the reference output on both concrete fixture argument sets.
These are primitive record checks, not a compiler-return or deployed equation. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ReferenceAdmission
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_RunJoin_FixtureArguments PV_RunJoin_FixtureAdmission

theorem transfer : WitnessOk
    (PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_RunJoin_ReferenceReturned.witness witness 600#u32 (some recipient) transferChange)) := by
  change WitnessOk (BuilderExtractedRecords.rawWitness
    (BuilderRecordsReference.witness input 600#u32
      ((some recipient).map PV_Src_RecordReference.note) (PV_Src_RecordReference.note transferChange)))
  exact BuilderRecordsAdmission.witness_ok _ _ _ _ transfer_values first second membership superRoot

theorem withdrawal : WitnessOk
    (PV_Src_Forest_PrimitiveArguments.wordWitness
      (PV_RunJoin_ReferenceReturned.witness witness 250#u32 none withdrawalChange)) := by
  change WitnessOk (BuilderExtractedRecords.rawWitness
    (BuilderRecordsReference.witness input 250#u32
      ((none : Option BuilderForestAdmissionPort.pool_v1.payment_relation.PoolV1OutputNoteWitnessV1).map
        PV_Src_RecordReference.note) (PV_Src_RecordReference.note withdrawalChange)))
  exact BuilderRecordsAdmission.witness_ok _ _ _ _ withdrawal_values first second membership superRoot

#print axioms transfer
#print axioms withdrawal
end R1Z.PV_RunJoin_ReferenceAdmission
