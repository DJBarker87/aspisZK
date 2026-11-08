import PV_LIB_SPEC_ContextContracts18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ConsumedHistory18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context initial)

/-- Monotonicity of consumed origins on the unchanged v2 machine, including
undefined decoder arms and every full reply. No successful-reply premise. -/
theorem step_member (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (x : Execution) (probe : Context) (member : probe ∈ x.consumed) :
    probe ∈ (PV_LIB_SPEC_ReachedNative14.step cut p x).consumed := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  cases ordinary : PV_LIB_SPEC_ControlRuntime.ordinary x.state with
  | none => simpa only [ordinary] using member
  | some pair =>
    obtain ⟨c,wait⟩ := pair
    simp only [ordinary]
    cases origin : PV_LIB_SPEC_ResourceHistory.context x c wait with
    | none => simpa only [origin] using member
    | some ctx =>
      simp only [origin]
      split <;> exact List.mem_cons_of_mem _ member

theorem run_member (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (n : Nat) (x : Execution) (probe : Context) (member : probe ∈ x.consumed) :
    probe ∈ (PV_LIB_SPEC_ReachedNative14.run cut p n x).consumed := by
  induction n generalizing x with
  | zero => exact member
  | succ n ih => exact ih _ (step_member cut p x probe member)

theorem prefix_member (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation n : Nat)
    (bound : n≤85) (probe : Context)
    (member : probe ∈ (PV_LIB_SPEC_History18.history entry activation n).consumed) :
    probe ∈ (PV_LIB_SPEC_History18.history entry activation 85).consumed := by
  change probe ∈ (PV_LIB_SPEC_ReachedNative14.run
    (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation))
    PV_LIB_SPEC_ReachedEnvironment14.parameters 85
    (initial (PV_LIB_SPEC_EntryWorld18.input entry.world))).consumed
  rw [← Nat.add_sub_of_le bound,PV_LIB_SPEC_Original14.run_add]
  exact run_member _ _ _ _ probe member

/-- Exact same-origin consumption, even when native decoding fails. -/
theorem poll_consumed (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (x : Execution) (c : Config) (wait : PV_STX2_Native.Waiting Data) (ctx : Context)
    (ordinary : PV_LIB_SPEC_ControlRuntime.ordinary x.state = some (c,wait))
    (origin : PV_LIB_SPEC_ResourceHistory.context x c wait = some ctx) :
    ctx ∈ (PV_LIB_SPEC_ReachedNative14.step cut p x).consumed := by
  unfold PV_LIB_SPEC_ReachedNative14.step
  simp only [ordinary]
  rw [origin]
  dsimp only
  split <;> exact List.mem_cons_self

#print axioms step_member
#print axioms run_member
#print axioms prefix_member
#print axioms poll_consumed
end PV_LIB_SPEC_ConsumedHistory18
