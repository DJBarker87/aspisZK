import PV_LIB_A_OwnerStoreV2
import PV_LIB_A_ArcPollV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WriterRegistryV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_THR2_SourceStoreLibrary
abbrev Event := PV_RJ4IDB.NativeEvent
abbrev Backend := PV_W1_OwnerNativeFrame.Backend

def RegistryFrame (before after : OWNER) : Prop :=
  after.next = before.next ∧ after.places = before.places ∧
    ∀ p, PV_EVHB_OwnerMachine.receiver after p = PV_EVHB_OwnerMachine.receiver before p

/-- Registry is proof instrumentation. The existing framed lift carries it
through EVERY native answer, without a post-world or success premise. -/
theorem native (H : Backend Event) (request : PV_STX2_Native.Request Data) (w : OWNER) :
    RegistryFrame w (PV_THR2_OwnUniformResourceHandler.lift H request w).world :=
  ⟨rfl,rfl,fun _ => rfl⟩

theorem primitive (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Backend Event) (values : Values OWNER Event) (c : Config) (w : OWNER)
    (es : List Event) (stack : List Config) (site : PV_LIB_A_StoreDispatchV2.Site)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : PV_LIB_A_StoreDispatchV2.select P c = some site) :
    RegistryFrame w (PV_LIB_A_StoreDispatchV2.step C K P resources encode
      (PV_THR2_OwnUniformResourceHandler.lift H) values ⟨⟨.running c,w,es⟩,stack⟩).current.world := by
  have effect := PV_LIB_A_StoreDispatchV2.effects C K P resources encode
    (PV_THR2_OwnUniformResourceHandler.lift H) values c w es stack site ordinary selected
  rw [effect.1]
  exact native H site.waiting.request w

theorem scope (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Backend Event) (values : Values OWNER Event) (c : Config) (w : OWNER)
    (es : List Event) (stack : List Config) (site : PV_LIB_A_ScopeDispatchV2.Site)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : PV_LIB_A_ScopeDispatchV2.select P c = some site) :
    RegistryFrame w (PV_LIB_A_ScopeDispatchV2.step C K P resources encode
      (PV_THR2_OwnUniformResourceHandler.lift H) values ⟨⟨.running c,w,es⟩,stack⟩).current.world := by
  have effect := PV_LIB_A_ScopeDispatchV2.effects C K P resources encode
    (PV_THR2_OwnUniformResourceHandler.lift H) values c w es stack site ordinary selected
  rw [effect.1]
  exact native H site.waiting.request w

theorem celltake (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Backend Event) (values : Values OWNER Event) (c : Config) (w : OWNER)
    (es : List Event) (stack : List Config) (site : PV_LIB_A_OwnerStoreV2.Site)
    (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : PV_LIB_A_OwnerStoreV2.select P c = some site) :
    RegistryFrame w (PV_LIB_A_OwnerStoreV2.step C K P resources encode
      (PV_THR2_OwnUniformResourceHandler.lift H) values ⟨⟨.running c,w,es⟩,stack⟩).current.world := by
  have effect := PV_LIB_A_OwnerStoreV2.effects C K P resources encode
    (PV_THR2_OwnUniformResourceHandler.lift H) values c w es stack site ordinary selected
  rw [effect.1]
  exact native H site.1.request w

/-- Actual12950 inherits the registry frame on the complete new candidate,
with no extra native frame or identity-delta assumption. -/
theorem arc12950 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Backend Event) (values : Values OWNER Event) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event) (stack : List Config)
    (leaf : P PV_THR2_Source361PacketChildren.fn63 = none) :
    RegistryFrame w (PV_LIB_A_OwnerStoreV2.step C K P resources encode
      (PV_THR2_OwnUniformResourceHandler.lift H) values
      ⟨⟨.running (PV_LIB_A_ArcPollV2.config s a parents),w,es⟩,stack⟩).current.world := by
  rw [PV_LIB_A_ArcPollV2.actual_poll C K P resources encode
    (PV_THR2_OwnUniformResourceHandler.lift H) values s a parents w es stack leaf]
  have effect := PV_LIB_A_StoreDispatchV2.effects C K P resources encode
    (PV_THR2_OwnUniformResourceHandler.lift H) values
    (PV_LIB_A_ArcPollV2.config s a parents) w es stack (PV_LIB_A_ArcPollV2.site s a)
    (by rfl) (PV_LIB_A_ArcPollV2.selected P s a parents leaf)
  simp only [PV_LIB_A_StoreDispatchV2.step,
    show PV_THR2_Catch316Segment.select (PV_LIB_A_ArcPollV2.config s a parents) = none from rfl,
    PV_LIB_A_ArcPollV2.selected P s a parents leaf] at effect
  rw [effect.1]
  exact native H (PV_LIB_A_ArcPollV2.site s a).waiting.request w

#print axioms native
#print axioms primitive
#print axioms scope
#print axioms celltake
#print axioms arc12950
end PV_LIB_A_WriterRegistryV2
