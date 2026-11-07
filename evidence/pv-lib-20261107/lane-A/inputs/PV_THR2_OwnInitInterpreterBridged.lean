import PV_THR2_OwnInitInterpreter
import PV_THR2_OwnInitAllocationHandlerBridged
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitInterpreterBridged
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
/-- NEW interpreter: exact allocation-site interpretation using the existing
full OwnInitAllocationHandlerBridged (thread21). All other sites use the retained operator
interpreter, including its three named operator facts and registration. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) :=
  match s.current.status with
  | .running c => if PV_THR2_OwnInitAction.selected c then
      PV_THR2_OperatorInterpreter.step C K P
        (PV_THR2_OwnInitAllocationHandlerBridged.handler resources encode H) s
    else PV_THR2_OperatorInterpreter.step C K P H s
  | _ => PV_THR2_OperatorInterpreter.step C K P H s
/-- Finite execution keeps the full current state and suspended stack. -/
def advance (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    Nat → PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent →
      PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent
  | 0,s => s
  | n+1,s => advance C K P resources encode H n (step C K P resources encode H s)
/-- ONE symbolic agreement outside the new call/retry sites, on every store,
world, source status and intrinsic stack. No global invariant is supplied. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (s : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent)
    (away : ∀ c, s.current.status = .running c → PV_THR2_OwnInitAction.selected c = false) :
    step C K P resources encode H s = PV_THR2_OperatorInterpreter.step C K P H s := by
  unfold step
  cases hs : s.current.status <;> try rfl
  rename_i c
  simp only [away c hs,Bool.false_eq_true,if_false]
/-- Same finite composition as the retained interpreter. -/
theorem advance_add (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (n m : Nat) (s : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) :
    advance C K P resources encode H (n+m) s =
      advance C K P resources encode H m (advance C K P resources encode H n s) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add,advance]
  | succ n ih => simpa only [Nat.succ_add,advance] using ih (step C K P resources encode H s)
#print axioms agreement
#print axioms advance_add
end PV_THR2_OwnInitInterpreterBridged
