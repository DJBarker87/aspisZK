import PV_LIB_SPEC_ActiveRead20
import PV_LIB_SPEC_ActiveAway20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveRequest20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_A_ActiveGetter17 (store154 token init)
open PV_LIB_A_F5FullEntry16 (activation parents)
open PV_LIB_SPEC_F1Arithmetic14 (stage)

theorem token_bound : store154.cells ⟨activation,8,[]⟩ = some token := by
  simp only [PV_LIB_A_ActiveGetter17.store154,PV_LIB_A_ActiveGetter17.store152,write]
  simp

theorem init_bound : store154.cells ⟨activation,9,[]⟩ = some init := write_same _ _ _

def at154 (e : Entry) (issued : List Issued) (consumed : List Context) : Execution :=
  stage store154 activation parents (PV_THR2_F170.live.body.drop 13) e.world [] issued consumed

def after (e : Entry) (issued : List Issued) (consumed : List Context) : Execution :=
  PV_LIB_SPEC_TlsRequest15.after store154 activation token init parents e.world [] issued consumed

/-- Exact issued469 request; existing named source request contract is reused.
No callee body and no Lane A join is proved here. -/
theorem issue (e : Entry) (a : Nat) (issued : List Issued) (consumed : List Context) :
    PV_LIB_A_ActiveEnvironment17.step
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
      PV_LIB_SPEC_ReachedEnvironment14.parameters (at154 e issued consumed) = after e issued consumed := by
  rw [PV_LIB_SPEC_ActiveAway20.step _ _ _ (by rfl)]
  exact PV_LIB_SPEC_TlsRequest15.request _ _ store154 activation token init parents
    e.world [] issued consumed token_bound init_bound

/-- One continuous original history, retaining the actual earlier origins. -/
theorem original (e : Entry) (a : Nat) :
    PV_LIB_SPEC_ActiveAdoption19.history e a 155 =
      after e (PV_LIB_SPEC_ActiveAdoption19.history e a 154).issued
        (PV_LIB_SPEC_ActiveAdoption19.history e a 154).consumed := by
  let q := PV_LIB_SPEC_ActiveAdoption19.history e a 154
  have eq : q = at154 e q.issued q.consumed :=
    PV_LIB_A_F170Return16.execution_ext _ _ (PV_LIB_SPEC_ActiveRead20.original e a) rfl rfl
  change PV_LIB_A_ActiveEnvironment17.run _ _ (154+1) _ = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change PV_LIB_A_ActiveEnvironment17.step _ _ q = _
  rw [eq]
  exact issue e a q.issued q.consumed

#print axioms token_bound
#print axioms init_bound
#print axioms at154
#print axioms after
#print axioms issue
#print axioms original
end PV_LIB_SPEC_ActiveRequest20
