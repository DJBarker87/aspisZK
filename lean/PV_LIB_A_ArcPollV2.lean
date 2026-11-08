import PV_LIB_A_OwnerStoreV2
import PV_LIB_A_ArcMemoryV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ArcPollV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_THR2_SourceStoreLibrary
abbrev State := PV_LIB_A_OwnerStoreV2.State
abbrev Handler := PV_LIB_A_OwnerStoreV2.Handler

def args (a : Nat) : List Data := [PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null]

def config (s : Store Data) (a : Nat) (parents : List Frame) : Config :=
  PV_THR2_IntrinsicFrameEnter.pending s a parents [] (PV_THR2_F361.live.body.drop 64)
    PV_THR2_Source361PacketChildren.fn63 (args a) 23

def site (s : Store Data) (a : Nat) : PV_LIB_A_StoreDispatchV2.Site :=
  ⟨.arcClone360,PV_THR2_Source361PacketChildren.fn63,
    PV_THR2_StaticReply.wait s PV_THR2_Source361PacketChildren.fn63 (args a) 23,args a⟩

/-- The ACTUAL12950 poll is selected with all generic metadata and source
operands intact. An expanded BODY is not intercepted as a native request. -/
theorem selected (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (leaf : P PV_THR2_Source361PacketChildren.fn63 = none) :
    PV_LIB_A_StoreDispatchV2.select P (config s a parents) = some (site s a) := by
  change (match P PV_THR2_Source361PacketChildren.fn63 with
    | some _ => none
    | none => some (site s a)) = _
  rw [leaf]

/-- Resolve SPEC-C3's local DISPATCH gap for the full reply. This states the
new count-action graph at12950, not original-entry reachability, last-strong
Drop adequacy, or full f361/OwnInit closure. -/
theorem actual_poll (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (leaf : P PV_THR2_Source361PacketChildren.fn63 = none) :
    PV_LIB_A_OwnerStoreV2.step C K P resources encode H values
      ⟨⟨.running (config s a parents),w,es⟩,stack⟩ =
      PV_LIB_A_StoreDispatchV2.deliver C (config s a parents) w es stack (site s a)
        (H (site s a).waiting.request w) := by
  have cellAway : PV_LIB_A_OwnerStoreV2.select P (config s a parents) = none := by
    change (match P PV_THR2_Source361PacketChildren.fn63 with
      | some _ => none | none => none) = _
    cases P PV_THR2_Source361PacketChildren.fn63 <;> rfl
  have scopeAway : PV_LIB_A_ScopeDispatchV2.select P (config s a parents) = none := by
    change (match P PV_THR2_Source361PacketChildren.fn63 with
      | some _ => none | none => none) = _
    cases P PV_THR2_Source361PacketChildren.fn63 <;> rfl
  have ordinary : PV_THR2_Catch316Segment.select (config s a parents) = none := rfl
  simp only [PV_LIB_A_OwnerStoreV2.step,cellAway,ordinary,
    PV_LIB_A_ScopeDispatchV2.step,scopeAway,PV_LIB_A_StoreDispatchV2.step,
    selected P s a parents leaf]

#print axioms selected
#print axioms actual_poll
end PV_LIB_A_ArcPollV2
