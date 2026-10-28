import R1Z.PV_RunJoin_ReferenceRootClosed
import R1Z.PV_RunJoin_FixtureArguments

/-! Exact fixture specializations of the reference equation. Their name and
statement intentionally retain Reference: the shipped mapper link is open. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ReferenceFixtureCalls
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open PV_RunJoin_ShippedExternal PV_RunJoin_FixtureArguments

abbrev R_reference := PV_RunJoin_RecordsReference.dictionary E_shipped

theorem transfer :
    @Records.call R_reference witness 600#u32 (some recipient) transferChange snapshot 77#u32 =
      @PV_Src_RecordDynamic.call E_shipped witness 600#u32 (some recipient) transferChange snapshot 77#u32 :=
  PV_RunJoin_RecordsReference.call_eq_dynamic _ _ _ _ _ _ _

theorem withdrawal :
    @Records.call R_reference witness 250#u32 none withdrawalChange snapshot 77#u32 =
      @PV_Src_RecordDynamic.call E_shipped witness 250#u32 none withdrawalChange snapshot 77#u32 :=
  PV_RunJoin_RecordsReference.call_eq_dynamic _ _ _ _ _ _ _

#print axioms transfer
#print axioms withdrawal
end R1Z.PV_RunJoin_ReferenceFixtureCalls
