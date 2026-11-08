import PV_LIB_SPEC_ActiveConsumption19
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ConsumedHistory19
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_A_ActiveEnvironment17 (step run Corrected)

theorem step_member (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (x : Execution) (probe : Context) (member : probe ∈ x.consumed) :
    probe ∈ (step cut p x).consumed := by
  classical
  by_cases corrected : Corrected x.state
  · unfold PV_LIB_A_ActiveEnvironment17.step
    rw [if_pos corrected]
    unfold PV_LIB_A_ActiveEnvironment17.corrected
    cases ordinary : PV_LIB_SPEC_ControlRuntime.ordinary x.state with
    | none => simpa only [ordinary] using PV_LIB_SPEC_ConsumedHistory18.step_member cut p x probe member
    | some pair =>
      obtain ⟨c,wait⟩ := pair
      simp only [ordinary]
      cases origin : PV_LIB_SPEC_ResourceHistory.context x c wait with
      | none => simpa only [origin] using PV_LIB_SPEC_ConsumedHistory18.step_member cut p x probe member
      | some ctx =>
        simp only [origin]
        split <;> exact List.mem_cons_of_mem _ member
  · rw [PV_LIB_A_ActiveEnvironment17.away cut p x corrected]
    exact PV_LIB_SPEC_ConsumedHistory18.step_member cut p x probe member

theorem run_member (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (n : Nat) (x : Execution) (probe : Context) (member : probe ∈ x.consumed) :
    probe ∈ (run cut p n x).consumed := by
  induction n generalizing x with
  | zero => exact member
  | succ n ih => exact ih _ (step_member cut p x probe member)

/-- Every actual native poll consumes its actual context, also at the repaired
callback and on the undefined/malformed arm. No invented8248 origin is added. -/
theorem poll_consumed (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (x : Execution) (c : Config) (wait : PV_STX2_Native.Waiting Data) (ctx : Context)
    (ordinary : PV_LIB_SPEC_ControlRuntime.ordinary x.state = some (c,wait))
    (origin : PV_LIB_SPEC_ResourceHistory.context x c wait = some ctx) :
    ctx ∈ (step cut p x).consumed := by
  classical
  by_cases corrected : Corrected x.state
  · unfold PV_LIB_A_ActiveEnvironment17.step
    rw [if_pos corrected]
    unfold PV_LIB_A_ActiveEnvironment17.corrected
    simp only [ordinary]
    rw [origin]
    dsimp only
    split <;> exact List.mem_cons_self
  · rw [PV_LIB_A_ActiveEnvironment17.away cut p x corrected]
    exact PV_LIB_SPEC_ConsumedHistory18.poll_consumed cut p x c wait ctx ordinary origin

/-- Arbitrary repaired-history prefix, preserving origins across every reply
and all future callback deliveries. Induction is symbolic, no loop replay. -/
theorem prefix_member (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation n m : Nat)
    (bound : n ≤ m) (probe : Context)
    (member : probe ∈ (PV_LIB_SPEC_ActiveAdoption19.history entry activation n).consumed) :
    probe ∈ (PV_LIB_SPEC_ActiveAdoption19.history entry activation m).consumed := by
  change probe ∈ (run (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation))
    PV_LIB_SPEC_ReachedEnvironment14.parameters m
    (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input entry.world))).consumed
  rw [← Nat.add_sub_of_le bound,PV_LIB_A_ActiveEnvironment17.run_add]
  exact run_member _ _ _ _ probe member

#print axioms step_member
#print axioms run_member
#print axioms poll_consumed
#print axioms prefix_member
end PV_LIB_SPEC_ConsumedHistory19
