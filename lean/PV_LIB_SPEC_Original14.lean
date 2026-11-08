import PV_LIB_SPEC_ReachedEnvironment14
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Original14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory

def site : Site := match PV_THR2_F0.node5 with
  | .leaf (.call site _ _ _ _) => site | _ => ⟨0,0,.null⟩
def after (s : Store Data) (a n : Nat) (f : Data) (w : OWNER) (es : List Event) : Execution :=
  ⟨⟨⟨.running ⟨PV_FN_THREAD_f0Entry.parent s a (.number n) f (.boolean true),[],
    PV_FN_THREAD_f0Entry.issued s a (.number n) f (.boolean true)⟩,w,es⟩,[]⟩,
    [⟨site,a,.child PV_THR2_RunEntryCall.callee s.nextActivation [.number n,f,.boolean true]⟩],[]⟩

/-- Exact source history as well as the interpreted state at step6. -/
theorem request (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a n : Nat) (f : Data) (w : OWNER) (es : List Event)
    (nCell : s.cells ⟨a,1,[]⟩ = some (.number n))
    (fCell : s.cells ⟨a,2,[]⟩ = some f)
    (literal : (runtime p).carrier.constant PV_THR2_RunEntryCall.flagDescriptor = some (.boolean true)) :
    PV_LIB_SPEC_ReachedNative14.run cut p 6 (initial ⟨s,a,n,f,w,es⟩) = after s a n f w es := by
  simp [PV_THR2_RunEntryCall.flagDescriptor,PV_THR2_F0.node5] at literal
  simp [after,site,PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_SPEC_ReachedNative14.run,PV_LIB_SPEC_ReachedNative14.step,
    PV_LIB_SPEC_ReachedNative14.control,PV_LIB_SPEC_ReachedNative14.transition,
    initial,PV_LIB_SPEC_F0Full.rootEntry,PV_LIB_SPEC_ControlRuntime.ordinary,
    PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OperatorAction.instruction,PV_THR2_OwnUniformBindings.step,
    PV_THR2_BindingRegister.register,PV_THR2_LocalBinding.selected,
    PV_THR2_IntrinsicState.step,PV_THR2_Catch316Segment.select,
    PV_THR2_Execution.step,PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf,
    PV_THR2_GapCompletion.step,PV_THR2_AggregateCompletion.complete,
    PV_STX2_SliceMachine.step,PV_THR2_F0.live,PV_THR2_F0.block12,
    PV_THR2_F0.node0,PV_THR2_F0.node1,PV_THR2_F0.node2,PV_THR2_F0.node3,
    PV_THR2_F0.node4,PV_THR2_F0.node5,native,adopt,PV_STX2_Native.step,
    PV_STX2_Store.bind,evaluate,operands,operand,PV_STX2_Store.read,locate,
    writeAddress,write,nCell,fCell,literal,
    PV_FN_THREAD_f0Entry.parent,PV_FN_THREAD_f0Entry.wait,PV_FN_THREAD_f0Entry.issued,
    PV_FN_THREAD_f0Entry.prepared,PV_THR2_StaticCall.issued,
    PV_STX2_Native.arguments,PV_THR2_RunEntryCall.callee]

/-- Same concrete input/world whose COMPLETE entry Pre was proved, and the
source literal is discharged rather than added as a new entry premise. -/
theorem original (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 6
      (initial PV_LIB_SPEC_Entry14.input) =
    after PV_LIB_SPEC_Entry13.store 1 1 PV_LIB_SPEC_ConcreteCaptures.closure
      PV_LIB_SPEC_Entry14.state [] :=
  request cut _ _ _ _ _ _ _ rfl rfl rfl

def bodyEntry (s : Store Data) (a n : Nat) (f : Data) (w : OWNER) (es : List Event) : Execution :=
  {after s a n f w es with state :=
    ⟨⟨.running ⟨{activation := s.nextActivation,remaining := PV_THR2_F1.live.body},
      [PV_FN_THREAD_f0Entry.parent s a (.number n) f (.boolean true)],
      PV_FN_THREAD_f0Entry.issued s a (.number n) f (.boolean true)⟩,w,es⟩,[]⟩}

theorem enter (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (s : Store Data) (a n : Nat) (f : Data) (w : OWNER) (es : List Event) :
    PV_LIB_SPEC_ReachedNative14.step cut p (after s a n f w es) = bodyEntry s a n f w es := by
  have different : PV_THR2_RunEntryCall.callee ≠ PV_THR2_Catch219Call318.fn := by
    intro h
    have eq := congrArg PV_THR2_OffPath.functionId h
    change some 1 = some 318 at eq
    cases eq
  have lookup : PV_LIB_SPEC_Full.programs PV_THR2_RunEntryCall.callee = some PV_THR2_F1.live := rfl
  simp [PV_LIB_SPEC_ReachedNative14.step,PV_LIB_SPEC_ReachedNative14.control,
    PV_LIB_SPEC_ReachedNative14.transition,after,bodyEntry,
    PV_FN_THREAD_f0Entry.parent,PV_FN_THREAD_f0Entry.wait,
    PV_LIB_SPEC_ControlRuntime.ordinary,lookup,different,
    PV_THR2_F0.live,PV_THR2_F0.block12,PV_THR2_F0.node6,
    PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,
    PV_LIB_StoreActionTable.step,PV_LIB_StoreActionTable.select,
    PV_THR2_OwnInitInterpreterBridged.step,PV_THR2_OwnInitAction.selected,
    PV_THR2_OperatorInterpreter.step,PV_THR2_OperatorAction.selected,
    PV_THR2_OwnUniformBindings.step,PV_THR2_BindingRegister.register,
    PV_THR2_LocalBinding.selected,PV_THR2_IntrinsicState.step,
    PV_THR2_Catch316Segment.select,PV_THR2_Execution.step,
    PV_THR2_Dynamic.active,PV_THR2_GapCompletion.step,PV_STX2_SliceMachine.step]

theorem run_add (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (n m : Nat) (x : Execution) :
    PV_LIB_SPEC_ReachedNative14.run cut p (n+m) x =
    PV_LIB_SPEC_ReachedNative14.run cut p m (PV_LIB_SPEC_ReachedNative14.run cut p n x) := by
  induction n generalizing x with
  | zero => simp only [Nat.zero_add,PV_LIB_SPEC_ReachedNative14.run]
  | succ n ih => simpa only [Nat.succ_add,PV_LIB_SPEC_ReachedNative14.run] using (ih (PV_LIB_SPEC_ReachedNative14.step cut p x))

theorem original_body (cut : PV_LIB_SPEC_ReachedNative14.Cut) :
    PV_LIB_SPEC_ReachedNative14.run cut PV_LIB_SPEC_ReachedEnvironment14.parameters 7
      (initial PV_LIB_SPEC_Entry14.input) =
    bodyEntry PV_LIB_SPEC_Entry13.store 1 1 PV_LIB_SPEC_ConcreteCaptures.closure
      PV_LIB_SPEC_Entry14.state [] := by
  rw [show 7=6+1 from rfl,run_add,original]
  exact enter cut _ _ _ _ _ _ _

#print axioms site
#print axioms after
#print axioms request
#print axioms original
#print axioms bodyEntry
#print axioms enter
#print axioms run_add
#print axioms original_body
end PV_LIB_SPEC_Original14
