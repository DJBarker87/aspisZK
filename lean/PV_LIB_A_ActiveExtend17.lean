import PV_LIB_A_ActivePrefix17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveExtend17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)

theorem extend (e : PV_LIB_SPEC_EntryWorld18.Entry) (a n delta : Nat) (before after : State)
    (reached : (PV_LIB_A_ActivePrefix17.history e a n).state = before)
    (segment : ∀ issued consumed,
      (PV_LIB_A_ActiveEnvironment17.run
        (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
        PV_LIB_SPEC_ReachedEnvironment14.parameters delta ⟨before,issued,consumed⟩).state = after) :
    (PV_LIB_A_ActivePrefix17.history e a (n+delta)).state = after := by
  let cut := PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a)
  let q := PV_LIB_A_ActivePrefix17.history e a n
  have hq : q = ⟨before,q.issued,q.consumed⟩ :=
    PV_LIB_A_F170Return16.execution_ext _ _ reached rfl rfl
  change (PV_LIB_A_ActiveEnvironment17.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters (n+delta)
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input e.world))).state = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change (PV_LIB_A_ActiveEnvironment17.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters delta q).state = _
  rw [hq]
  exact segment q.issued q.consumed

#print axioms extend
end PV_LIB_A_ActiveExtend17
