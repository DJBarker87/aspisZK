import PV_LIB_SPEC_ThreadSpecifications
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_F316Callback
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Row PV_LIB_SPEC_Frozen
/-- f316 may be invoked by the intrinsic with NO ordinary caller frame. Its
actual saved caller is then in suspended. Nonempty ordinary callers remain
covered by the SAME row, with their original saved waiting action. -/
structure Input where
  store : Store Data
  activation : Nat
  argument : Data
  callers : List Frame
  world : OWNER
  events : List Event
  suspended : List Config

def entry (i : Input) : State :=
  ⟨⟨.running ⟨{activation := i.activation,remaining := PV_THR2_F316.live.body},i.callers,i.store⟩,
    i.world,i.events⟩,i.suspended⟩
def view (i : Input) : PV_LIB_SPEC_Row.Input :=
  ⟨i.store,i.activation,[i.argument],i.callers.headD {activation := 0,remaining := []},
    i.callers.drop 1,0,⟨.child .null i.activation [i.argument],.child i.activation (.local 0),[]⟩,
    i.world,i.events,i.suspended⟩
abbrev MachineSpec := PV_LIB_SPEC_Frozen.MachineSpec

def Pre (p : Parameters) (i : Input) : Prop :=
  i.store.cells ⟨i.activation,1,[]⟩ = some i.argument ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.store.nextActivation ∧
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed i.world i.activation ∧
  RegisteredValidity i.world ∧ Numbered (entry i) ∧ References (runtime p) (view i) ∧
  (match i.callers with
    | [] => True
    | parent :: _ => ∃ wait dest, parent.waiting = some wait ∧
        wait.action = .child i.activation (.local dest))

def ReturnDestination (i : Input) (address : Address) : Prop :=
  ∃ parent parents wait dest, i.callers = parent :: parents ∧ parent.waiting = some wait ∧
    wait.action = .child i.activation (.local dest) ∧ address = ⟨parent.activation,dest,[]⟩

def Frame (p : Parameters) (i : Input) (q : State) : Prop :=
  let s := PV_W1_LeafBoundary.statusStore q.current.status
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed q.current.world s.nextActivation ∧
  Numbered q ∧ (∃ own, q.suspended = own ++ i.suspended) ∧
  (∃ suffix, q.current.events = i.events ++ suffix) ∧
  ∀ address : Address, address.activation < i.activation → ¬ ReturnDestination i address →
    ¬ PV_W1_ArgumentEffects.Writable (runtime p).carrier
      ⟨i.store,i.activation,i.callers,[],[],.null,[i.argument],0,i.suspended⟩ i.world address →
      s.cells address = i.store.cells address

/-- Actual raw data pointer/capture read, call220 and union/result-cell write;
all source effects and every reply branch, including a callback left pending.
Completion before the intrinsic's resume administration is this row's boundary. -/
def Post (table : FullStoreActionTable) (p : Parameters) (i : Input)
    (candidate : Nat → State) : Prop :=
  let m := source table p
  PV_LIB_SPEC_Frontier.Behavior m (entry i) candidate ∧
  ∀ k, (∀ j, j < k → ¬ PV_LIB_SPEC_Frontier.Boundary m (entry i) candidate j) →
    ¬ PV_LIB_SPEC_Frontier.Aborts (candidate k) → Frame p i (candidate k)

def Contract (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table p m → Pre p i → Post table p i (implementation m i)

/-- Source-segment construction used at the actual intrinsic invocation. This
is a data projection, not a proof that the caller discharges the entire Pre. -/
def intrinsicInput (before : State) (segment : PV_THR2_CallbackSegment.Segment)
    (argument : Data) : Input :=
  ⟨segment.callback.store,segment.callback.frame.activation,argument,
    segment.callback.callers,before.current.world,before.current.events,
    segment.suspended :: before.suspended⟩

def ordinaryInput (i : PV_LIB_SPEC_Row.Input) : Input :=
  ⟨i.store,i.activation,i.arguments.headD .null,i.parent :: i.parents,
    i.world,i.events,i.suspended⟩

def Comparison (table : FullStoreActionTable) (p : Parameters)
    (implementation : Machine → Input → Nat → State) : Prop :=
  PV_LIB_SPEC_F316Full.PackageStatement ∧ Contract table p implementation ∧
  (∀ i, PV_LIB_SPEC_Frozen.F316.Pre p i → Pre p (ordinaryInput i))

#print axioms Input
#print axioms entry
#print axioms view
#print axioms MachineSpec
#print axioms Pre
#print axioms ReturnDestination
#print axioms Frame
#print axioms Post
#print axioms Contract
#print axioms intrinsicInput
#print axioms ordinaryInput
#print axioms Comparison
end PV_LIB_SPEC_F316Callback
