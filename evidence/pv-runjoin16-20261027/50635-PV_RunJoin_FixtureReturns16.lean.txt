import R1Z.PV_RunJoin_CompilerDictionary16
import R1Z.PV_RunJoin_ReferenceFixtureResults
set_option autoImplicit false
namespace R1Z.PV_RunJoin_FixtureReturns16
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open BuilderForestAdmissionPort.pool_v1 PV_RunJoin_FixtureArguments
open PV_RunJoin_ReferenceFixtureResults PV_RunJoin_CompilerDictionary16

theorem transfer :
    @Records.call shipped witness 600#u32 (some recipient) transferChange snapshot 77#u32 =
      ok (transferWitness,transferPublic) := by
  rw [dictionary]
  exact (PV_RunJoin_ReferenceFixtureCalls.transfer).symm.trans PV_RunJoin_ReferenceFixtureResults.transfer

theorem withdrawal :
    @Records.call shipped witness 250#u32 none withdrawalChange snapshot 77#u32 =
      ok (withdrawalWitness,withdrawalPublic) := by
  rw [dictionary]
  exact (PV_RunJoin_ReferenceFixtureCalls.withdrawal).symm.trans PV_RunJoin_ReferenceFixtureResults.withdrawal

theorem transfer_new :
    @pair_forest_copy_builder.CopyRecords.new shipped witness 600#u32 (some recipient)
      transferChange snapshot 77#u32 = ok ⟨transferWitness,transferPublic⟩ := by
  unfold pair_forest_copy_builder.CopyRecords.new pair_forest_copy_builder.records
  rw [transfer]; rfl

theorem withdrawal_new :
    @pair_forest_copy_builder.CopyRecords.new shipped witness 250#u32 none
      withdrawalChange snapshot 77#u32 = ok ⟨withdrawalWitness,withdrawalPublic⟩ := by
  unfold pair_forest_copy_builder.CopyRecords.new pair_forest_copy_builder.records
  rw [withdrawal]; rfl

#print axioms transfer
#print axioms withdrawal
#print axioms transfer_new
#print axioms withdrawal_new
end R1Z.PV_RunJoin_FixtureReturns16
