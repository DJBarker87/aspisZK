import PV_LIB_A_OwnerStoreV3
import PV_THR2_OwnUniformNeutral
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_PreActionTraceV3
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
abbrev State := PV_LIB_A_OwnerStoreV3.State
abbrev Handler := PV_LIB_A_OwnerStoreV3.Handler
/-- Prefix-local SOURCE SHAPE certificates. All OWNER layers must be neutral;
this does not assert that the corrected machine is the raw interpreter. In
particular14320 and14756 do NOT satisfy this predicate. -/
def Quiet (P : Data → Option PV_STX2_SliceSyntax.Program) (s : State) : Prop :=
  PV_LIB_A_OwnerStoreV3.Neutral P s ∧
  ∀ c, s.current.status = .running c →
    PV_THR2_OwnInitAction.selected c = false ∧
    PV_THR2_OperatorAction.selected c = none ∧
    PV_THR2_OwnUniformNeutral.configuration c

/-- Compose the existing OWNER and operator neutralities BY NAME, retaining
registration and the resource/bridged allocation layer at every action site. -/
theorem step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (quiet : Quiet P s) :
    PV_LIB_A_OwnerStoreV3.step C K P resources encode H values s =
      PV_THR2_IntrinsicState.step C K P H s := by
  rw [PV_LIB_A_OwnerStoreV3.agreement C K P resources encode H values s quiet.1,
    PV_THR2_OwnInitInterpreterBridged.agreement C K P resources encode H s
      (fun c hs => (quiet.2 c hs).1)]
  have operators : PV_THR2_OperatorInterpreter.step C K P H s =
      PV_THR2_OwnUniformBindings.step C K P H s := by
    unfold PV_THR2_OperatorInterpreter.step
    cases hs : s.current.status <;> try rfl
    rename_i c
    simp only [(quiet.2 c hs).2.1]
  rw [operators]
  exact PV_THR2_OwnUniformNeutral.step C K P H s (fun c hs => (quiet.2 c hs).2.2)

def Trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) : Nat → State → Prop
  | 0,_ => True
  | n+1,s => Quiet P s ∧ Trace C K P H n (PV_THR2_IntrinsicState.step C K P H s)

/-- ONE induction over this actual finite pre-action trace. No store is folded
or compared, and no global future-control invariant is introduced. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) (s : State)
    (trace : Trace C K P H n s) :
    PV_LIB_A_OwnerStoreV3.advance C K P resources encode H values n s =
      PV_THR2_IntrinsicState.advance C K P H n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change PV_LIB_A_OwnerStoreV3.advance C K P resources encode H values n
      (PV_LIB_A_OwnerStoreV3.step C K P resources encode H values s) = _
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

/-- All native selectors are neutral at any source instruction/completion.
This covers ONLY the native-action layer, not the OWNER guards in Quiet. -/
theorem nonwaiting (P : Data → Option PV_STX2_SliceSyntax.Program)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (waiting : c.frame.waiting = none) :
    PV_LIB_A_OwnerStoreV3.Neutral P ⟨⟨.running c,w,es⟩,stack⟩ := by
  intro d running
  cases running
  unfold PV_LIB_A_OwnerStoreV3.select PV_LIB_A_ScopeDispatchV2.select
    PV_LIB_A_StoreDispatchV2.select PV_THR2_SourceStoreNative.select
  cases completed : c.frame.completed <;> simp [waiting]

#print axioms step
#print axioms run
#print axioms append
#print axioms nonwaiting
end PV_LIB_A_PreActionTraceV3
