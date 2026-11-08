import PV_LIB_SPEC_ActiveAdoption19
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_HistoryExtend20
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_EntryWorld18 (Entry)
open PV_LIB_SPEC_ActiveAdoption19 (history)

/-- Complete history composition. The segment is a proved run equality,
not a post-store or allocator premise installed on the machine. -/
theorem full (e : Entry) (a n delta : Nat) (before : State)
    (out : List Issued → List Context → Execution)
    (reached : (history e a n).state = before)
    (segment : ∀ issued consumed,
      PV_LIB_A_ActiveEnvironment17.run
        (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame e a))
        PV_LIB_SPEC_ReachedEnvironment14.parameters delta ⟨before,issued,consumed⟩ =
        out issued consumed) :
    history e a (n+delta) = out (history e a n).issued (history e a n).consumed := by
  let q := history e a n
  have eq : q = ⟨before,q.issued,q.consumed⟩ :=
    PV_LIB_A_F170Return16.execution_ext q ⟨before,q.issued,q.consumed⟩ reached rfl rfl
  change PV_LIB_A_ActiveEnvironment17.run _ _ (n+delta) _ = _
  rw [PV_LIB_A_ActiveEnvironment17.run_add]
  change PV_LIB_A_ActiveEnvironment17.run _ _ delta q = _
  calc
    _ = PV_LIB_A_ActiveEnvironment17.run _ _ delta ⟨before,q.issued,q.consumed⟩ := congrArg _ eq
    _ = out q.issued q.consumed := segment q.issued q.consumed

#print axioms full
end PV_LIB_SPEC_HistoryExtend20
