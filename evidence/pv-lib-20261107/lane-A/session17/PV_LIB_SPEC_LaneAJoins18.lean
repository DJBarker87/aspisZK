import PV_LIB_SPEC_History18
import PV_LIB_SPEC_LaneAJoins16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_LaneAJoins18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution initial)

open PV_LIB_SPEC_EntryWorld18 (Entry)
/-- Same v2 with the chosen complete physical entry and granted stack base. -/
abbrev history := PV_LIB_SPEC_History18.history

def BodyEntry (q : Execution) (body : List PV_STX2_SliceSyntax.Node) : Prop :=
  ∃ c, q.state.current.status = .running c ∧ c.frame.remaining = body ∧
    c.frame.waiting = none ∧ c.frame.completed = none ∧ c.frame.unwinding = none

def OriginalToF6 (entry : Entry) (activation : Nat) : Prop :=
  ∃ n6, 85 ≤ n6 ∧ BodyEntry (history entry activation n6) PV_THR2_F6.live.body

def RangeEntry (q : Execution) : Prop :=
  ∃ (s : Store Data) (a : Nat) (parents : List Frame),
    q.state.current.status = .running (PV_THR2_Source15LoopEnter.after s a parents)

def F6ToRange (entry : Entry) (activation : Nat) (n6 : Nat) : Prop :=
  ∃ delta, RangeEntry (history entry activation (n6+delta))

def RangeToF361 (entry : Entry) (activation : Nat) (nr : Nat) : Prop :=
  ∃ delta, BodyEntry (history entry activation (nr+delta)) PV_THR2_F361.live.body

/-- Source milestones only. Payload, decoded words, physical registers and
ownership are NOT supplied as hypotheses. Lane C derives them at these cuts. -/
def F361ToInit (entry : Entry) (activation : Nat) (n361 : Nat) : Prop :=
  ∃ (callbackN registrationN readyN pollN : Nat) (callback registration ready : Config),
    n361 ≤ callbackN ∧ callbackN < registrationN ∧ registrationN < readyN ∧
    readyN+1 = pollN ∧
    (history entry activation callbackN).state.current.status = .running callback ∧
    callback.frame.remaining = PV_THR2_F361.live.body.drop 92 ∧
    (history entry activation registrationN).state.current.status = .running registration ∧
    registration.frame.activation = callback.frame.activation ∧
    registration.frame.remaining = PV_THR2_F361.live.body.drop 113 ∧
    (history entry activation readyN).state.current.status = .running ready ∧
    ready.frame.activation = callback.frame.activation ∧
    PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129) ready ∧
    PV_LIB_SPEC_OwnInitFull.InitPoll (history entry activation pollN).state

/-- Joint join target, not an assumed endpoint premise or an inhabitant.
Each existential must be EXHIBITED, with calls contracted and loops inducted. -/
def Joins (entry : Entry) (activation : Nat) : Prop :=
  ∃ n6 nr n361, 85 ≤ n6 ∧ n6 ≤ nr ∧ nr ≤ n361 ∧
    BodyEntry (history entry activation n6) PV_THR2_F6.live.body ∧
    RangeEntry (history entry activation nr) ∧
    BodyEntry (history entry activation n361) PV_THR2_F361.live.body ∧ F361ToInit entry activation n361

/-- Lane C supplies this parametric prefix by name. No later milestone is
assumed. Lane A must exhibit its indices on this exact continuation. -/
theorem original85 (entry : Entry) (activation : Nat) :
    history entry activation 85 = PV_LIB_SPEC_World18_Tls85Data16.at85 entry :=
  PV_LIB_SPEC_History18.original85 entry activation

#print axioms history
#print axioms BodyEntry
#print axioms OriginalToF6
#print axioms RangeEntry
#print axioms F6ToRange
#print axioms RangeToF361
#print axioms F361ToInit
#print axioms Joins
#print axioms original85
end PV_LIB_SPEC_LaneAJoins18
