import R1Z.PV_RunJoin_ReferenceReturned
import R1Z.PV_RunJoin_ReferenceFixtureCalls
import R1Z.PV_RunJoin_ReferenceAdmission

/-! Reference outputs and primitive admission for the fixture arguments. This
provides no shipped dictionary or native compiler success equation. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ReferenceFixtureResults
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort R0Z.WriterRefine
open PV_RunJoin_FixtureArguments PV_RunJoin_ReferenceFixtureCalls

def transferWitness := PV_RunJoin_ReferenceReturned.witness witness 600#u32 (some recipient) transferChange
def withdrawalWitness := PV_RunJoin_ReferenceReturned.witness witness 250#u32 none withdrawalChange
def transferPublic := PV_RunJoin_ReferenceReturned.publicRecord (some recipient) snapshot 77#u32
def withdrawalPublic := PV_RunJoin_ReferenceReturned.publicRecord none snapshot 77#u32

theorem transfer : @Records.call R_reference witness 600#u32 (some recipient) transferChange snapshot 77#u32 =
    ok (transferWitness,transferPublic) := PV_RunJoin_ReferenceReturned.call _ _ _ _ _ _

theorem withdrawal : @Records.call R_reference witness 250#u32 none withdrawalChange snapshot 77#u32 =
    ok (withdrawalWitness,withdrawalPublic) := PV_RunJoin_ReferenceReturned.call _ _ _ _ _ _

theorem transfer_checked : WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness transferWitness) :=
  PV_RunJoin_ReferenceAdmission.transfer

theorem withdrawal_checked : WitnessOk (PV_Src_Forest_PrimitiveArguments.wordWitness withdrawalWitness) :=
  PV_RunJoin_ReferenceAdmission.withdrawal

#print axioms transfer
#print axioms withdrawal
#print axioms transfer_checked
#print axioms withdrawal_checked
end R1Z.PV_RunJoin_ReferenceFixtureResults
