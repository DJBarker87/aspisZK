import PV_FN_THREAD_f361BoxBridged
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Bridged443
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_OWN2_Codec
/-- Reconstruction from the ACTUAL f443 return cell. -/
def reboxed (symbols : PV_THR2_OperatorSemantics_14119.Symbols) (value : Data) : Data :=
  PV_FN_THREAD_f361BoxCodecGap.boxedCallback
    (PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612.value
      (PV_THR2_OperatorSemantics_14121.result (PV_THR2_OperatorSemantics_14119.result symbols value)))
    PV_THR2_Box458Prefix5.allocator
/-- Instantiate CLOSED443 at14113 on the actual callback allocation world.
In each successful134/344 branch the actual full returned store supplies the
source pointer to the14119/14121 and612/f458 constructors. Decoding is proved
in443's actual post-world, with its backend effects retained. The subsequent
source-instruction/call-entry joins in f361 remain separate obligations. -/
theorem at14113 (x : PV_FN_THREAD_f361BoxCallees.Input PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (s : Store Data) (w : OWNER)
    (backend : PV_STX_World.World) (symbols : PV_THR2_OperatorSemantics_14119.Symbols)
    (handle data : Pointer)
    (answer : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok data.val)) (nonnull : data.val ≠ 0)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed
      (withWorld (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world backend)
      x.s.nextActivation) :
    let allocated := (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world
    let y := {x with w := withWorld allocated backend}
    let child := PV_FN_THREAD_f361BoxCallees.child443 y (PV_THR2_PacketBoxBacking.root s)
    PV_FN_THREAD_f443.Post child ∧
    (PV_FN_THREAD_f443Entry13.Returned134 child →
      PV_FN_THREAD_f443Entry13.Returned344 child →
      ∃ d, (PV_FN_THREAD_f443Entry13.q13 child).current.status = .running d ∧
        PV_THR2_OwnInitSourceCodec.decodeBridged
          (PV_FN_THREAD_f443Entry13.q13 child).current.world
          (PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
            [PV_THR2_OwnInitPointerCodec.encode handle,
              reboxed symbols (((PV_FN_THREAD_f443.final child d).cells
                ⟨x.a,38,[]⟩).getD .null)]) = some ⟨handle,data,symbols.vtable_115⟩) := by
  intro allocated y child
  have closed := PV_FN_THREAD_f361BoxCallees.callee443 y (PV_THR2_PacketBoxBacking.root s) owner
  refine ⟨closed,?_⟩
  intro ret134 ret344
  dsimp only [child] at ret134 ret344
  have successful := closed
  simp only [PV_FN_THREAD_f443.Post,if_pos ret134,if_pos ret344] at successful
  obtain ⟨d,status,reached,frame,value⟩ := successful.2.2
  obtain ⟨postBackend,postWorld⟩ := closed.1
  have binding := PV_THR2_ClosureBoxRegistry.binding resources encode s w data answer nonnull
  have atPost : PV_THR2_BoxDynRepresentationBridge.runtime
      (PV_FN_THREAD_f443Entry13.q13 child).current.world (PV_THR2_PacketBoxBacking.root s) = some data := by
    rw [postWorld]
    exact binding
  refine ⟨d,status,?_⟩
  change (PV_FN_THREAD_f443.final child d).cells ⟨x.a,38,[]⟩ =
    some (PV_STX2_TypedReferences.reference (PV_THR2_PacketBoxBacking.root s) .null) at value
  rw [value]
  exact PV_THR2_OwnInitSourceCodec.source _ symbols _ handle data atPost
#print axioms at14113
end PV_FN_THREAD_f361Bridged443
