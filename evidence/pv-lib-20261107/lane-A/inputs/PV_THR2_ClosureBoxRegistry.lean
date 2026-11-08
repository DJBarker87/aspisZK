import PV_THR2_ClosureBoxActivationReply
import PV_THR2_OwnInitSourceCodecBridged
set_option autoImplicit false
noncomputable section
namespace PV_THR2_ClosureBoxRegistry
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner PV_OWN2_Codec
/-- Internal returned resource branch, not an assumed registry association.
The actual allocation registers the source-minted argument backing, then
installs the actual returned address in that same header. -/
theorem binding (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (p : Pointer)
    (answer : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok p.val)) (nonnull : p.val ≠ 0) :
    PV_THR2_BoxDynRepresentationBridge.runtime
      (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world
      (PV_THR2_PacketBoxBacking.root s) = some p := by
  unfold PV_THR2_ClosureBoxAllocation.reply
  have ans := PV_THR2_PacketBoxResource.answer resources encode s w
    PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment
  rw [PV_THR2_ClosureBoxAllocation.request_size,answer] at ans
  rw [PV_THR2_PacketBoxReply.returned _ _ _ _ _ ans nonnull]
  have places : (PV_THR2_PacketBoxResource.reply resources encode s w
      PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment).world.places
      (PV_THR2_BoxDynRepresentationBridge.sourcePlace (PV_THR2_PacketBoxBacking.root s)) =
      some w.next := by
    rw [PV_THR2_PacketBoxResource.all]
    simp only [PV_THR2_PacketBoxRegister.backend,PV_THR2_ClosureBoxAllocation.request_size,
      answer,if_neg nonnull]
    change (if (⟨s.nextActivation,[1]⟩ : PV_EVHB_OwnerMachine.Place) =
      ⟨s.nextActivation,[1]⟩ then some w.next else _) = _
    rw [if_pos rfl]
  simp only [PV_THR2_BoxDynRepresentationBridge.runtime,receiver,places,
    Option.bind_some,install_lookup,Option.map_some,Bind.bind,
    capacityStore,pointerStore,PV_THR2_OwnInitPointerCodec.decode,dif_pos p.isLt]

/-- The14756 source ThreadInit value using the f443-derived reference and
actual612/f458 constructors decodes in the allocation's actual post-world.
The only hypotheses are the named LEAF allocation returned branch and nonnull;
no Shape, decoder-success, registry-binding or adequacy hypothesis occurs. -/
theorem decoded14756 (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (handle p : Pointer)
    (answer : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok p.val)) (nonnull : p.val ≠ 0) :
    PV_THR2_OwnInitSourceCodec.decodeBridged
      (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world
      (PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
        [PV_THR2_OwnInitPointerCodec.encode handle,
          PV_THR2_BoxDynRepresentationBridge.callback symbols
            (PV_THR2_PacketBoxBacking.root s)]) = some ⟨handle,p,symbols.vtable_115⟩ :=
  PV_THR2_OwnInitSourceCodec.source _ symbols _ handle p
    (binding resources encode s w p answer nonnull)
#print axioms binding
#print axioms decoded14756
end PV_THR2_ClosureBoxRegistry
