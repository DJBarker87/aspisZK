import PV_THR2_OwnInitAllocationReply
import PV_THR2_OwnUniformReceiverFrame
import PV_THR2_BoxTyped
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitAllocationOwned
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_STX2_SliceMachine PV_EVHB_OwnerMachine PV_EVHB_RawVecOwner PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Conditional on owner acceptance of amended translator. Hypotheses:
FreshAllocationValidity' at the source binding's registered pre-state, and the
actual nonzero successful resource case. No supplied receiver or endpoint.
The local14756 reply conversion consumes BoxTyped.init_memory BY NAME. Source
entry transport and installation of this reply interpretation remain open. -/
theorem returned (C : Carrier OWNER Data) (store : Store Data) (a : Nat)
    (parents : List Frame) (s : OWNER) (resources : Resources) (encode : Encode)
    (granted : GrantedRegions) (p handle callback vtable : Pointer)
    (valid : FreshAllocationValidity' resources granted
      (PV_THR2_BindingRegister.register
        ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,store⟩ s))
    (answer : (resources (.malloc 24) (world s)).answer = .returned (.ok p.val))
    (nonnull : p.val ≠ 0) :
    let c := Config.mk {activation := a,remaining := PV_THR2_F361.live.body.drop 113} parents store
    let pre := PV_THR2_BindingRegister.register c s
    let r := PV_THR2_OwnInitAllocationReply.reply resources encode pre s.next
      (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) ⟨handle,callback,vtable⟩
    r.answer = .returned (.ok (PV_THR2_OwnInitPointerCodec.encode p)) ∧
      PV_OWN2_ThreadInitLayout.InitMemory r.world ⟨⟨a,[45]⟩,[⟨handle,callback,vtable⟩]⟩ := by
  let c := Config.mk {activation := a,remaining := PV_THR2_F361.live.body.drop 113} parents store
  let pre := PV_THR2_BindingRegister.register c s
  let h := PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8
  have registered := PV_THR2_OwnUniformReceiverFrame.registered store a parents s
  have header : lookup pre.world s.next = some h := registered.2.header
  have back : world pre = world s := registered.1
  have reply : (resources (.malloc 24) (world pre)).answer = .returned (.ok p.val) := by rw [back]; exact answer
  have eqpre : pre = PV_THR2_BoxRegister.register C c s s :=
    PV_THR2_BindingRegister.export_prestate C store a parents s s
  have typed := PV_THR2_BoxTyped.init_memory
    (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit) (OsString := Unit) (Scope := Unit)
    C c s s resources encode granted p.val handle callback vtable
    (by rw [← eqpre]; exact valid) (by rw [← eqpre]; exact reply) nonnull
  have exactRun := PV_OWN2_ConstructorSuccess.init_success_run resources encode pre s.next h p.val
    handle callback vtable header reply nonnull
  dsimp only at typed
  rw [← eqpre] at typed
  rw [exactRun] at typed
  have counted := PV_OWN2_CountedAllocation.malloc_success resources encode pre s.next 24 p.val h header reply nonnull
  have primitiveAnswer : (PV_EVHB_OwnerHeap.primitive resources encode s.next (.malloc 24) pre).answer = .returned (.ok p.val) := by
    simp only [PV_EVHB_OwnerHeap.primitive,header,reply]
  dsimp only [PV_THR2_OwnInitAllocationReply.reply]
  rw [counted,PV_THR2_OwnInitAllocationReply.returned _ _ _ _ p primitiveAnswer nonnull]
  exact ⟨rfl,typed.2⟩
#print axioms returned
end PV_THR2_OwnInitAllocationOwned
