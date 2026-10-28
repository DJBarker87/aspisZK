import R1Z.PV_Src_RootHelper
import R1Z.PV_RunJoin_RecordsAdapter16
import R1Z.PV_RunJoin_FixtureArguments
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WithdrawalIdentification16
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort
open PV_RunJoin_ShippedExternal PV_RunJoin_FixtureArguments

theorem withdrawal :
    @Records.call (PV_RunJoin_RecordsAdapter16.R_shipped PV_Src_CanonicalRoots.table)
      witness 250#u32 none withdrawalChange snapshot 77#u32 =
    @PV_Src_RecordDynamic.call E_shipped
      witness 250#u32 none withdrawalChange snapshot 77#u32 := by
  unfold PV_Src_RecordDynamic.call PV_Src_RecordReference.call
  rw [show @pool_v1.pair_trace.pair_empty_roots E_shipped =
    ok PV_Src_CanonicalRoots.table from PV_Src_RootHelper.source]
  simp only [bind_tc_ok]
  rw [BuilderRecordsReference.records]
  simp only [PV_RunJoin_RecordsAdapter16.R_shipped, Records.call,
    PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.records,
    PV_RunJoin_Records.pool_v1.pair_forest_copy_builder.records.owned,
    PV_RunJoin_RecordsAdapter16.raw_owned_all_words, lift, bind_tc_ok]
  with_unfolding_all rfl

#print axioms withdrawal
end R1Z.PV_RunJoin_WithdrawalIdentification16
