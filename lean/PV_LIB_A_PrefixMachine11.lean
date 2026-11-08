import PV_LIB_A_DeferredActions
import PV_THR2_OwnUniformNeutral
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PrefixMachine11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- Control-shape certificate only; registration14320 and allocation14756 are
exceptional steps and cannot be hidden in a neutral prefix. -/
def Quiet (P : Data → Option PV_STX2_SliceSyntax.Program) (s : State) : Prop :=
  SourceNeutral P s ∧ ∀ c, s.current.status = .running c →
    PV_THR2_OwnInitAction.selected c = false ∧
    PV_THR2_OperatorAction.selected c = none ∧
    PV_THR2_OwnUniformNeutral.configuration c

theorem step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (quiet : Quiet P s) :
    PV_LIB_A_DeferredActions.step C K P resources encode H values ⟨s,none⟩ =
      ⟨PV_THR2_IntrinsicState.step C K P H s,none⟩ := by
  rw [PV_LIB_A_DeferredActions.agreement C K P resources encode H values s quiet.1,
    PV_THR2_OwnInitInterpreterBridged.agreement C K P resources encode H s
      (fun c hs => (quiet.2 c hs).1)]
  have operators : PV_THR2_OperatorInterpreter.step C K P H s =
      PV_THR2_OwnUniformBindings.step C K P H s := by
    unfold PV_THR2_OperatorInterpreter.step
    cases hs : s.current.status <;> try rfl
    rename_i c
    simp only [(quiet.2 c hs).2.1]
  rw [operators,PV_THR2_OwnUniformNeutral.step C K P H s
    (fun c hs => (quiet.2 c hs).2.2)]

def Trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) : Nat → State → Prop
  | 0,_ => True
  | n+1,s => Quiet P s ∧ Trace C K P H n (PV_THR2_IntrinsicState.step C K P H s)

def advance (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) : Nat → SourceState → SourceState
  | 0,s => s
  | n+1,s => advance C K P resources encode H values n
      (PV_LIB_A_DeferredActions.step C K P resources encode H values s)

/-- One trace-indexed induction; no global bisimulation or callee counter
identity. Each consumer must discharge the finite control-shape certificate. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) (s : State)
    (trace : Trace C K P H n s) :
    advance C K P resources encode H values n ⟨s,none⟩ =
      ⟨PV_THR2_IntrinsicState.advance C K P H n s,none⟩ := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change advance C K P resources encode H values n
      (PV_LIB_A_DeferredActions.step C K P resources encode H values ⟨s,none⟩) = _
    rw [step C K P resources encode H values s trace.1]
    exact ih _ trace.2

theorem append (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler)
    (n m : Nat) (s : State) (first : Trace C K P H n s)
    (tail : Trace C K P H m (PV_THR2_IntrinsicState.advance C K P H n s)) :
    Trace C K P H (n+m) s := by
  induction n generalizing s with
  | zero => simpa only [Nat.zero_add,PV_THR2_IntrinsicState.advance] using tail
  | succ n ih =>
    rw [Nat.succ_add]
    exact ⟨first.1,ih _ first.2 tail⟩

theorem advance_add (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n m : Nat) (s : SourceState) :
    advance C K P resources encode H values (n+m) s =
      advance C K P resources encode H values m
        (advance C K P resources encode H values n s) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add,advance]
  | succ n ih =>
    simpa only [Nat.succ_add,advance] using ih (PV_LIB_A_DeferredActions.step C K P resources encode H values s)

#print axioms step
#print axioms run
#print axioms append
#print axioms advance_add
end PV_LIB_A_PrefixMachine11
