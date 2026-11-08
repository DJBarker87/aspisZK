import PV_LIB_A_WriterOrdinary
import PV_LIB_A_OwnerStoreTransport
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WriterRegistry
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_W1_LeafBoundary
open PV_THR2_SourceStoreLibrary
/-- All five source writers preserve the actual registry under the existing
native backend lift, without a separately supplied catch or registry frame.
Allocation/registration source instructions retain their own OWNER actions. -/
theorem installed (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : PV_W1_OwnerNativeFrame.Backend PV_RJ4IDB.NativeEvent)
    (values : Values OWNER PV_RJ4IDB.NativeEvent) (e : Entry)
    (f : PV_THR2_SourceStoreNative.Function) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (leaf : P e.callee = none)
    (meaning : PV_THR2_SourceStoreNative.function e.callee = some f) :
    let out := PV_LIB_A_OwnerStore.step C K P resources encode
      (PV_THR2_OwnUniformResourceHandler.lift H) values
      ⟨⟨.running (pending e),w,es⟩,e.suspended⟩
    out.current.world.next = w.next ∧ out.current.world.places = w.places ∧
      ∀ p, PV_EVHB_OwnerMachine.receiver out.current.world p = PV_EVHB_OwnerMachine.receiver w p :=
  PV_LIB_A_OwnerStoreTransport.registry C K P resources encode H values (pending e) w es
    e.suspended (PV_LIB_A_WriterSites.site e f) (PV_LIB_A_WriterOrdinary.noncatch e f meaning)
    (PV_LIB_A_WriterSites.selected P e f leaf meaning)
#print axioms installed
end PV_LIB_A_WriterRegistry
