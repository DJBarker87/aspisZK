import PV_LIB_SPEC_ConsumedHistory18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ValuesPrefix18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)
open PV_LIB_SPEC_History18 (history)

def NoWriter (request : PV_STX2_Native.Request Data) : Prop :=
  match request with
  | .child fn _ _ => PV_LIB_StoreActionTable.v2 fn = none
  | _ => True

/-- The complete five-origin inventory proved on the rebased history.
No source or native writer is smuggled past the prefix. -/
theorem final_absent (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation : Nat)
    (ctx : Context) (member : ctx ∈ (history entry activation 85).consumed) : NoWriter ctx.request := by
  rw [PV_LIB_SPEC_History18.replies85] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem prefix_absent (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation n : Nat)
    (bound : n≤85) (ctx : Context) (member : ctx ∈ (history entry activation n).consumed) :
    NoWriter ctx.request :=
  final_absent entry activation ctx
    (PV_LIB_SPEC_ConsumedHistory18.prefix_member entry activation n bound ctx member)

/-- Every actual source-context native poll before85 has no v2 action.
Thus no IntoIter9/append10/push167 Values operation is invoked in this prefix.
This does NOT assert coverage for the unknown suffix85..14756. -/
theorem poll_absent (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation n : Nat)
    (bound : n<85) (c : Config) (wait : PV_STX2_Native.Waiting Data) (ctx : Context)
    (ordinary : PV_LIB_SPEC_ControlRuntime.ordinary (history entry activation n).state = some (c,wait))
    (origin : PV_LIB_SPEC_ResourceHistory.context (history entry activation n) c wait = some ctx) :
    NoWriter ctx.request := by
  have member := PV_LIB_SPEC_ConsumedHistory18.poll_consumed
    (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation))
    PV_LIB_SPEC_ReachedEnvironment14.parameters (history entry activation n) c wait ctx ordinary origin
  have next : history entry activation (n+1) =
      PV_LIB_SPEC_ReachedNative14.step
        (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation))
        PV_LIB_SPEC_ReachedEnvironment14.parameters (history entry activation n) := by
    rw [history,PV_LIB_SPEC_Original14.run_add]
    rfl
  rw [← next] at member
  exact prefix_absent entry activation (n+1) (by omega) ctx member

#print axioms NoWriter
#print axioms final_absent
#print axioms prefix_absent
#print axioms poll_absent
end PV_LIB_SPEC_ValuesPrefix18
