import PV_LIB_A_OwnerStore
import PV_W1_OwnerNativeFrame
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_OwnerStoreTransport
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_OwnerStore
/-- Trace exclusion follows the retained OWNER interpreter, with every intrinsic
stack and every outcome retained. It does not assert exclusion for OwnInit. -/
def NeutralTrace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) : Nat → State → Prop
  | 0,_ => True
  | n+1,s => (∀ c, s.current.status = .running c → PV_THR2_SourceStoreNative.select P c = none) ∧
      NeutralTrace C K P resources encode H n
        (PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s)

theorem advance_add (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n m : Nat) (s : State) :
    PV_LIB_A_OwnerStore.advance C K P resources encode H values (n+m) s =
      PV_LIB_A_OwnerStore.advance C K P resources encode H values m (PV_LIB_A_OwnerStore.advance C K P resources encode H values n s) := by
  induction n generalizing s with
  | zero => simp only [Nat.zero_add,PV_LIB_A_OwnerStore.advance]
  | succ n ih => simpa only [Nat.succ_add,PV_LIB_A_OwnerStore.advance] using ih (PV_LIB_A_OwnerStore.step C K P resources encode H values s)

/-- Single induction transports unmodified OWNER runs that avoid writer calls. -/
theorem advance_agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) (s : State)
    (trace : NeutralTrace C K P resources encode H n s) :
    PV_LIB_A_OwnerStore.advance C K P resources encode H values n s =
      PV_THR2_OwnInitInterpreterBridged.advance C K P resources encode H n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change PV_LIB_A_OwnerStore.advance C K P resources encode H values n (PV_LIB_A_OwnerStore.step C K P resources encode H values s) = _
    rw [agreement C K P resources encode H values s trace.1]
    exact ih _ trace.2

theorem segment (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) (s out : State)
    (trace : NeutralTrace C K P resources encode H n s)
    (proved : PV_THR2_OwnInitInterpreterBridged.advance C K P resources encode H n s = out) :
    PV_LIB_A_OwnerStore.advance C K P resources encode H values n s = out :=
  (advance_agreement C K P resources encode H values n s trace).trans proved

/-- Native source writes preserve the registry by the actual existing backend
lift, with no assumption about the native answer or post-backend state. -/
theorem registry (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_W1_OwnerNativeFrame.Backend PV_RJ4IDB.NativeEvent)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : PV_THR2_SourceStoreNative.Site)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : PV_THR2_SourceStoreNative.select P c = some site) :
    let out := PV_LIB_A_OwnerStore.step C K P resources encode (PV_THR2_OwnUniformResourceHandler.lift H)
      values ⟨⟨.running c,w,es⟩,stack⟩
    out.current.world.next = w.next ∧ out.current.world.places = w.places ∧
      ∀ p, PV_EVHB_OwnerMachine.receiver out.current.world p = PV_EVHB_OwnerMachine.receiver w p := by
  intro out
  have framed := effects C K P resources encode (PV_THR2_OwnUniformResourceHandler.lift H)
    values c w es stack site ordinary selected
  change out.current.world = _ ∧ _ at framed
  rw [framed.1]
  exact ⟨rfl,rfl,fun _ => rfl⟩
#print axioms advance_add
#print axioms advance_agreement
#print axioms segment
#print axioms registry
end PV_LIB_A_OwnerStoreTransport
