import PV_LIB_SPEC_TlsAt85
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_LaneAJoins16
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution initial)

/-- All joins use this ONE original input, environment, resolver and v2 step.
The native frame is finite data to be constructed by lane C, not a new world. -/
def history (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (n : Nat) : Execution :=
  PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
    PV_LIB_SPEC_ReachedEnvironment14.parameters n (initial PV_LIB_SPEC_Entry14.input)

def BodyEntry (q : Execution) (body : List PV_STX2_SliceSyntax.Node) : Prop :=
  ∃ c, q.state.current.status = .running c ∧ c.frame.remaining = body ∧
    c.frame.waiting = none ∧ c.frame.completed = none ∧ c.frame.unwinding = none

def OriginalToF6 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) : Prop :=
  ∃ n6, 85 ≤ n6 ∧ BodyEntry (history stack n6) PV_THR2_F6.live.body

def RangeEntry (q : Execution) : Prop :=
  ∃ (s : Store Data) (a : Nat) (parents : List Frame),
    q.state.current.status = .running (PV_THR2_Source15LoopEnter.after s a parents)

def F6ToRange (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (n6 : Nat) : Prop :=
  ∃ delta, RangeEntry (history stack (n6+delta))

def RangeToF361 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (nr : Nat) : Prop :=
  ∃ delta, BodyEntry (history stack (nr+delta)) PV_THR2_F361.live.body

/-- Source milestones only. Payload, decoded words, physical registers and
ownership are NOT supplied as hypotheses. Lane C derives them at these cuts. -/
def F361ToInit (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (n361 : Nat) : Prop :=
  ∃ (callbackN registrationN readyN pollN : Nat) (callback registration ready : Config),
    n361 ≤ callbackN ∧ callbackN < registrationN ∧ registrationN < readyN ∧
    readyN+1 = pollN ∧
    (history stack callbackN).state.current.status = .running callback ∧
    callback.frame.remaining = PV_THR2_F361.live.body.drop 92 ∧
    (history stack registrationN).state.current.status = .running registration ∧
    registration.frame.activation = callback.frame.activation ∧
    registration.frame.remaining = PV_THR2_F361.live.body.drop 113 ∧
    (history stack readyN).state.current.status = .running ready ∧
    ready.frame.activation = callback.frame.activation ∧
    PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129) ready ∧
    PV_LIB_SPEC_OwnInitFull.InitPoll (history stack pollN).state

/-- Joint join target, not an assumed endpoint premise or an inhabitant.
Each existential must be EXHIBITED, with calls contracted and loops inducted. -/
def Joins (stack : PV_LIB_SPEC_PhysicalStack12.Frame) : Prop :=
  ∃ n6 nr n361, 85 ≤ n6 ∧ n6 ≤ nr ∧ nr ≤ n361 ∧
    BodyEntry (history stack n6) PV_THR2_F6.live.body ∧
    RangeEntry (history stack nr) ∧
    BodyEntry (history stack n361) PV_THR2_F361.live.body ∧ F361ToInit stack n361

/-- Existing result supplied by lane C, with no successful-native premise. -/
theorem original85 (stack : PV_LIB_SPEC_PhysicalStack12.Frame) :
    history stack 85 = PV_LIB_SPEC_Tls85Data16.at85 := PV_LIB_SPEC_TlsAt85.original85 stack

#print axioms history
#print axioms BodyEntry
#print axioms OriginalToF6
#print axioms RangeEntry
#print axioms F6ToRange
#print axioms RangeToF361
#print axioms F361ToInit
#print axioms Joins
#print axioms original85
end PV_LIB_SPEC_LaneAJoins16
