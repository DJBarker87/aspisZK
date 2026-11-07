import PV_FN_THREAD_f361Statement
import PV_THR2_SourceStoreInterpreter
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_RegistrationGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev State := PV_THR2_IntrinsicState.State OWNER Event
/-- The actual emitted storage-live14320, not a fabricated native request. -/
def before (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List Event) (stack : List Config) : State :=
  ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,s⟩,
    w,es⟩,stack⟩
/-- Literal frozen COMMON interpreter omits the established OWNER action. -/
theorem raw_next (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER Event Data)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List Event) (stack : List Config) :
    (PV_THR2_SourceStoreInterpreter.step C K P H values
      (before s a parents w es stack)).current.world.next = w.next := rfl
/-- Existing package semantics registers the source-selected descriptor. -/
theorem registered_next (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER Event Data)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List Event) (stack : List Config) :
    (PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H
      (before s a parents w es stack)).current.world.next = w.next+1 := rfl
/-- A checked local model mismatch for every world and environment. This does
not assert reachability from original entry or contradiction of decodeBridged. -/
theorem steps_differ (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (resources : Resources) (encode : Encode)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER Event Data)
    (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List Event) (stack : List Config) :
    PV_THR2_SourceStoreInterpreter.step C K P H values (before s a parents w es stack) ≠
    PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H
      (before s a parents w es stack) := by
  intro equal
  have same := congrArg (fun q : State => q.current.world.next) equal
  rw [raw_next,registered_next] at same
  omega
/-- The two exact step equations cannot be demanded jointly at this site.
This is not the full original-entry joint-nonemptiness proposition. -/
def JointStep (candidate : State → State) (q raw registered : State) : Prop :=
  candidate q = raw ∧ candidate q = registered
#print axioms raw_next
#print axioms registered_next
#print axioms steps_differ
#print axioms JointStep
end PV_LIB_SPEC_RegistrationGap
