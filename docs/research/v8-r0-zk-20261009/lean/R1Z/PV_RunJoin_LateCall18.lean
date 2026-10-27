import R1Z.PV_RunJoin_LateAppend18
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LateCall18
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open PV_RunJoin_ReferenceFixtureResults PV_RunJoin_AppendNative17
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem transfer : (do
    let pair ← pair_forest_copy_builder.CopyRecords.output_pair ⟨transferWitness,transferPublic⟩
    pair_forest_trace.late_append ⟨transferWitness,transferPublic⟩ PV_RunJoin_FixtureArguments.snapshot pair) =
      ok (.Ok (PV_RunJoin_LateAppend18.result transfer0 transfer20)) := by
  rw [PV_RunJoin_OutputPair17.transfer]
  simp only [bind_tc_ok]
  exact PV_RunJoin_LateAppend18.transfer
#print axioms transfer

theorem withdrawal : (do
    let pair ← pair_forest_copy_builder.CopyRecords.output_pair ⟨withdrawalWitness,withdrawalPublic⟩
    pair_forest_trace.late_append ⟨withdrawalWitness,withdrawalPublic⟩ PV_RunJoin_FixtureArguments.snapshot pair) =
      ok (.Ok (PV_RunJoin_LateAppend18.result withdrawal0 withdrawal20)) := by
  rw [PV_RunJoin_OutputPair17.withdrawal]
  simp only [bind_tc_ok]
  exact PV_RunJoin_LateAppend18.withdrawal
#print axioms withdrawal
end R1Z.PV_RunJoin_LateCall18
