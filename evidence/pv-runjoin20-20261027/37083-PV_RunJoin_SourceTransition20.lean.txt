import R1Z.PV_RunJoin_CompilerTotal20
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SourceTransition20
open Aeneas Aeneas.Std
open BuilderForestAdmissionPort.pool_v1

theorem transfer : PV_Src_NativeInput.transition
    ⟨PV_RunJoin_FixtureArguments.snapshot,PV_RunJoin_LateAppend18.result
      PV_RunJoin_AppendNative17.transfer0 PV_RunJoin_AppendNative17.transfer20⟩ =
    PV_RunJoin_RecordedTransfer.transition := by
  with_unfolding_all rfl
#print axioms transfer

theorem withdrawal : PV_Src_NativeInput.transition
    ⟨PV_RunJoin_FixtureArguments.snapshot,PV_RunJoin_LateAppend18.result
      PV_RunJoin_AppendNative17.withdrawal0 PV_RunJoin_AppendNative17.withdrawal20⟩ =
    PV_RunJoin_RecordedWithdrawal.transition := by
  with_unfolding_all rfl
#print axioms withdrawal
end R1Z.PV_RunJoin_SourceTransition20
