import PV_THR2_ClosureBoxRegistry
import PV_FN_THREAD_f361BoxCodecGap
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361BoxBridged
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_OWN2_Codec
/-- slice10: arbitrary native backend effects retain the registry address. -/
theorem backend_binding (w : OWNER) (backend : PV_STX_World.World) (p : Address) :
    PV_THR2_BoxDynRepresentationBridge.runtime (withWorld w backend) p =
      PV_THR2_BoxDynRepresentationBridge.runtime w p := rfl

/-- LOCAL14313 context, with the callback allocation's actual post-world.
CLOSED458 is instantiated BY NAME. The callback is its actual returned Box,
not an assumed numeric Shape. The physical data word is derived from13923;
CLOSED443's output reference is fed through the exact14119/14121 casts.
Full f361 entry-to-this-context reachability is a separate join obligation. -/
theorem at14313 (x : PV_FN_THREAD_f361BoxCallees.Input PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (s : Store Data) (w : OWNER)
    (backend : PV_STX_World.World) (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (handle p : Pointer)
    (answer : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok p.val)) (nonnull : p.val ≠ 0)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed
      (withWorld (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world backend)
      x.s.nextActivation)
    (unique612 : PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612.Fact x.native) :
    let allocated := (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world
    let y := {x with w := withWorld allocated backend}
    let raw := PV_THR2_OperatorSemantics_14121.result
      (PV_THR2_OperatorSemantics_14119.result symbols
        (PV_STX2_TypedReferences.reference (PV_THR2_PacketBoxBacking.root s) .null))
    let child := PV_FN_THREAD_f361BoxCallees.child458 y raw
    PV_FN_THREAD_f458.PostWithPointer child ∧
    (∀ unique, (PV_FN_THREAD_f537.reply (PV_FN_THREAD_f458Entry.child child)).answer =
      .returned (.ok unique) →
      PV_THR2_OwnInitSourceCodec.decodeBridged y.w
        (PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
          [PV_THR2_OwnInitPointerCodec.encode handle,
            PV_FN_THREAD_f361BoxCodecGap.boxedCallback unique PV_THR2_Box458Prefix5.allocator]) =
        some ⟨handle,p,symbols.vtable_115⟩) := by
  intro allocated y raw child
  have closed := PV_FN_THREAD_f361BoxCallees.callee458 y raw owner unique612
  refine ⟨closed,?_⟩
  intro unique returned
  have pointer := (closed.2 unique returned).1
  have binding := (backend_binding allocated backend (PV_THR2_PacketBoxBacking.root s)).trans
    (PV_THR2_ClosureBoxRegistry.binding resources encode s w p answer nonnull)
  change PV_THR2_BoxDynRepresentationBridge.runtime y.w (PV_THR2_PacketBoxBacking.root s) = some p at binding
  have bridge : PV_THR2_BoxDynRepresentationBridge.decode y.w
      (PV_FN_THREAD_f361BoxCodecGap.boxedCallback unique PV_THR2_Box458Prefix5.allocator) =
      some (p,symbols.vtable_115) := by
    change PV_THR2_BoxDynRepresentationBridge.sourceWords y.w
      (PV_THR2_Box537Suffix13.boxed unique PV_THR2_Box458Prefix5.allocator) = _
    unfold PV_THR2_BoxDynRepresentationBridge.sourceWords
    rw [pointer]
    change (PV_STX2_TypedReferences.decode (PV_STX2_TypedReferences.reference
      (PV_THR2_PacketBoxBacking.root s) .null) >>= fun pair =>
      PV_THR2_BoxDynRepresentationBridge.runtime y.w pair.1 >>= fun d =>
      PV_THR2_OwnInitPointerCodec.decode (PV_THR2_OperatorSemantics_14119.vtable_115 symbols) >>=
        fun v => some (d,v)) = _
    simp only [PV_STX2_TypedReferences.roundtrip,Bind.bind,Option.bind_some,binding,
      PV_THR2_OperatorSemantics_14119.vtable_115,PV_THR2_OwnInitPointerCodec.roundtrip]
  simp only [PV_THR2_OwnInitSourceCodec.decodeBridged,PV_THR2_KeyValues.pack,
    List.map_cons,List.map_nil,ite_true,PV_THR2_OwnInitPointerCodec.roundtrip,
    bridge,Bind.bind,Option.bind_some,Pure.pure]
#print axioms backend_binding
#print axioms at14313
end PV_FN_THREAD_f361BoxBridged
