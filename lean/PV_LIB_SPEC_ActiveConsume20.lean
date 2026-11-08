import PV_LIB_SPEC_ActiveOrigin20
import PV_LIB_SPEC_ActiveDelivery20
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveConsume20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_SPEC_ActivePoll20 (config wait request)
open PV_LIB_SPEC_ActiveOrigin20 (origin)

def after (e : Entry) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨PV_LIB_SPEC_ActiveDelivery20.after e,
    (PV_LIB_SPEC_ActiveRequest20.after e issued consumed).issued,origin consumed :: consumed⟩

/-- Actual native context consumption, complete source/physical state and
origins retained. The reply is computed, not a hypothesis. -/
theorem consume (e : Entry) (a : Nat) (issued : List Issued) (consumed : List Context) :
    PV_LIB_A_ActiveEnvironment17.step
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
      PV_LIB_SPEC_ReachedEnvironment14.parameters
      (PV_LIB_SPEC_ActiveRequest20.after e issued consumed) = after e issued consumed := by
  rw [PV_LIB_A_ActiveEnvironment17.away _ _ _ (PV_LIB_SPEC_ActiveOrigin20.away e issued consumed)]
  unfold PV_LIB_SPEC_ReachedNative14.step
  rw [PV_LIB_SPEC_ActivePoll20.ordinary]
  dsimp only
  rw [PV_LIB_SPEC_ActiveOrigin20.context]
  dsimp only
  let resources : PV_EVHB_OwnerHeap.Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment (origin consumed)
  change (match PV_LIB_SPEC_ReachedNative14.answer _
    (PV_LIB_A_ActiveTlsNative17.parameters resources) config request e.world with
    | none => _ | some _ => _) = _
  rw [PV_LIB_SPEC_ActivePoll20.answer e a resources]
  change (⟨PV_LIB_SPEC_ReachedNative14.transition _
    (PV_LIB_A_ActiveTlsNative17.parameters resources) config
      ⟨⟨.running config,e.world,[]⟩,[]⟩,_,_⟩ : Execution) = _
  rw [PV_LIB_SPEC_ActiveDelivery20.transition]
  rfl

theorem original (e : Entry) (a : Nat) :
    PV_LIB_SPEC_ActiveAdoption19.history e a 156 =
      after e (PV_LIB_SPEC_ActiveAdoption19.history e a 154).issued
        (PV_LIB_SPEC_ActiveAdoption19.history e a 154).consumed := by
  change PV_LIB_A_ActiveEnvironment17.run _ _ (155+1) _ = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change PV_LIB_A_ActiveEnvironment17.step _ _ (PV_LIB_SPEC_ActiveAdoption19.history e a 155) = _
  rw [PV_LIB_SPEC_ActiveRequest20.original]
  exact consume e a _ _

#print axioms after
#print axioms consume
#print axioms original
end PV_LIB_SPEC_ActiveConsume20
