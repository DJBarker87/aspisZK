import PCD_Row320
import PCD_RequestRoot
set_option autoImplicit false
noncomputable section
namespace PCM_Inst_TerminalSource
open Aeneas Aeneas.Std
/-- Source-carrier group: the exact CLOSED model, with all of its inputs.
Transport to PCM/RSL views is a separate named map obligation. -/
abbrev LaneArgs := PCD_LaneRef.Lane × PCD_Row320.TerminalResult
def laneModel (a : LaneArgs) := PCD_Row320.RowSpec_POOL_320 a.1 a.2

def laneLaw (a : LaneArgs) (out : PCD.Exit PCD_LaneRef.Lane) : Prop :=
  True ∧ out = laneModel a

theorem lane_graph (a : LaneArgs) (out : PCD.Exit PCD_LaneRef.Lane) :
    laneLaw a out ↔ True ∧ out = laneModel a := Iff.rfl

theorem lane_native (a : LaneArgs) {State : Type} (state : State) :
    (PCD_Row320.nativeSegments a.1 a.2,state,([] : List PCD.Event)) =
      (.ok (laneModel a),state,[]) :=
  PCD_Row320.result_state_effects a.1 a.2 state

/-- The infallible allocation observation is retained as an actual argument;
it is neither fixed to success nor identified with fallible reservation. -/
abbrev RequestArgs := Slice U8 × PCD_Request.Allocation
def requestModel (a : RequestArgs) := PCD_RequestRoot.RowSpec_POOL_314 a.1 a.2

def requestLaw (a : RequestArgs) (out : PCD_BoxFold.Execution (Slice U8) PCD_Request.Request PCD_BoxFold.RequestError) : Prop :=
  True ∧ out = requestModel a

theorem request_native (a : RequestArgs) {State : Type} (state : State) :
    (PCD_BoxFold.source a.1 a.2,state) = (requestModel a,state) :=
  PCD_RequestRoot.result_state_effects a.1 a.2 state

#print axioms lane_graph
#print axioms lane_native
#print axioms request_native
end PCM_Inst_TerminalSource
