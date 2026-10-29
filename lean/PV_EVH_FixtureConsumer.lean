import PV_EVH_Deployed
import PV_RJ4IDB_CallerLive
import NDR_CombinedAudit
/-! adopted by owner decision D502/D478. LEAD-ONLY 16 GiB aggregation consumer.
DO NOT compile in the pv-evh worker's 8 GiB scope. Source reference: research
merge 06f74c902f. FixturePdaRuntime is deliberately explicit and unproved. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVH_FixtureConsumer
open AspisR1 Aeneas Aeneas.Std Result
open R1Z.PrivacyR1HeadlineDeployedEvents
open AspisR1.NDR_CombinedAudit

/-- adopted by owner decision D502/D478. Concrete complete event adversary
carrier: arbitrary adaptive programs and decisions see the public option-B
signal and the full ordered event observation, including terminal prefixes. -/
abbrev DeployedAdversary := PV_EVH_Core.Observer (Option PV_RJ4IDB.Bytes) PV_RJ4IDB.Bytes

/-- adopted by owner decision D502/D478. Concrete byte-handle caller statement
for the two-transaction fixture path. Native record/handle association remains
separate; this does not identify every live request with transfer-13. -/
def deployedStatement (handle : PV_RJ4IDB.Bytes) :=
  R1Z.PV_RJ4IDB_CallerLive.callerStatement handle

/-- adopted by owner decision D502/D478. V047's model public fibre at the
explicit statement. It does not discharge a native caller association. -/
theorem public_fibre (handle : PV_RJ4IDB.Bytes) :
    ∃ w : R1Z.PV_RJDec_V047.H.Instance,
      R1Z.PV_RJDec_V047.H.public w = (deployedStatement handle).1 :=
  R1Z.PV_RJ4IDB_CallerLive.caller_witness handle

/-- adopted by owner decision D502/D478. V045–V047 fixture execution witness:
the exact installed headline SDK, one saved checkpoint, both TX1 worlds and
TX2 acceptance. This retains the original FixturePdaRuntime base hypothesis;
it establishes neither native privacy links nor arbitrary live reachability. -/
theorem two_transaction_nonvacuity
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second
        (AdapterRw.r1_pool_adapter.owned.stage2_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) := by
  exact AspisR1.NDR_CombinedAudit.sourceOnHeadline base stage slot runtime

#print axioms public_fibre
#print axioms two_transaction_nonvacuity
end PV_EVH_FixtureConsumer
