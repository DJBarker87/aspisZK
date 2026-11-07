import PV_W5_F31Child
import PV_STX2_ToVecF31Suffix
set_option autoImplicit false
set_option pp.proofs false
noncomputable section
namespace PV_FN_SLICE_f31
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OWNER PV_EVHB_RawVecOwner
open PV_STX2_SliceMachine

structure Pre (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER) : Prop where
  wellFormed : PV_STX2_OwnerActivationWellFormed.OwnerWellFormed w s.nextActivation
  live : a<s.nextActivation
  usize : n<PV_STX2_Source7CapacityScalars.modulus
  length : s.cells ⟨a,1,[]⟩=some (.number n)
  allocator : s.cells ⟨a,2,[]⟩=some PV_STX2_Source7GlobalClone.value
  layout : s.cells ⟨a,3,[]⟩=some PV_STX2_Source7LayoutConstructor.value
  registered : ∃ id h, (PV_STX2_Source7QUniformBindings.target parents).bind w.places=some id ∧
    lookup w.world id=some h ∧ h.shape.width=4 ∧ PV_EVHB_OwnerReserve.alignment h.shape.align=4

abbrev L (ctrl : Control) := PV_STX2_Source7QF31Assert.control (PV_STX2_Source7QAllocationCall.control ctrl)
abbrev childReply (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend) :=
  PV_W5_F31Child.reply resources encode base (L ctrl) s parents a n w external backend

def handler (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend) : PV_W5_F35Modes.HType :=
  fun q w => by
    classical
    exact if q=.child PV_STX2_Source7ConstructorEntry.callee s.nextActivation
      [.number n,PV_STX2_Source7ConstructorEntry.initValue,PV_STX2_Source7GlobalClone.value,PV_STX2_Source7LayoutConstructor.value]
    then childReply resources encode base ctrl s parents a n w external backend
    else PV_STX2_Source7QUniformResourceHandler.lift backend q w

def C (base : Carrier PV_STX_World.World Data) (ctrl : Control) (H : PV_W5_F35Modes.HType) :=
  PV_STX2_Source7ConstructorEntry.carrier (PV_STX2_Source7QUniformReturnCompatibility.C base (L ctrl) H)

def start (s : Store Data) (parents : List Frame) (a : Nat) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent) :
    Prefix OWNER PV_RJ4IDB.NativeEvent :=
  ⟨.running ⟨{activation:=a,remaining:=PV_STX2_Source7CtorF31.program.body},parents,s⟩,w,prior⟩

def errorReply (s : Store Data) (value : Data) (w : OWNER) (backend : PV_W5_NativeFrame.Backend) :=
  PV_STX2_Source7QUniformResourceHandler.lift backend
    (.child PV_W5_NativeLeaves.callee_f36 (s.nextActivation+1) [(PV_FN_SLICE_f35.firstSlot value).getD .null]) w

/-- Fixed stopping time derived from full replies: 8 through the f35 reply,
43 through successful f31 return, 13 through the f36 reply, or22 through abort.
No earlier issued-request prefix can witness Post. -/
def fuel (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend) : Nat :=
  let r := childReply resources encode base ctrl s parents a n w external backend
  match r.answer with
  | .returned (.ok value) =>
    if (L ctrl).variant value=some 0 then 43
    else match (errorReply s value r.world backend).answer with
      | .returned (.ok _) => 22
      | _ => 13
  | _ => 8

def outcome (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parents : List Frame) (a n : Nat) (w : OWNER) (prior : List PV_RJ4IDB.NativeEvent)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend) :=
  let H := handler resources encode base ctrl s parents a n external backend
  PV_STX2_Source7IterationBindings.advance resources encode (C base ctrl H) (L ctrl) (fun _ => none) H
    (fuel resources encode base ctrl s parents a n w external backend) (start s parents a w prior)

def Boundary (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend)
    (out : Prefix OWNER PV_RJ4IDB.NativeEvent) : Prop :=
  match out.status with
  | .undefined _ _ | .returned _ _ => False
  | .fault _ _ => True
  | .running c =>
    c.frame.activation=a ∧ c.callers=parent::parents ∧
    match c.frame.completed with
    | some (.ok value) =>
      (∃ pointer, value=PV_W5_F35Success.inner pointer n PV_STX2_Source7GlobalClone.value) ∧
      (childReply resources encode base ctrl s (parent::parents) a n w external backend).answer=
        .returned (.ok (PV_STX2_Source7QConstructorResult.value value)) ∧
      out.world=(childReply resources encode base ctrl s (parent::parents) a n w external backend).world
    | some (.fail _) | some .div => True
    | none => ∃ waiting, c.frame.waiting=some waiting ∧
      (waiting.request=.child PV_STX2_Source7ConstructorEntry.callee s.nextActivation
        [.number n,PV_STX2_Source7ConstructorEntry.initValue,PV_STX2_Source7GlobalClone.value,PV_STX2_Source7LayoutConstructor.value] ∨
       ∃ error, waiting.request=.child PV_W5_NativeLeaves.callee_f36 (s.nextActivation+1) [error])

def Post (resources : Resources) (encode : Encode) (base : Carrier PV_STX_World.World Data) (ctrl : Control)
    (s : Store Data) (parent : Frame) (parents : List Frame) (a n : Nat) (w : OWNER)
    (prior : List PV_RJ4IDB.NativeEvent) (external : PV_W5_NoAllocShim.External) (backend : PV_W5_NativeFrame.Backend) : Prop :=
  let out := outcome resources encode base ctrl s (parent::parents) a n w prior external backend
  fuel resources encode base ctrl s (parent::parents) a n w external backend ≤ 43 ∧
    Boundary resources encode base ctrl s parent parents a n w external backend out ∧
    PV_W5_F59Frame.Post s a w out ∧ (∃ suffix, out.events=prior++suffix) ∧
    PV_FN_SLICE_f35.Post resources encode base (L ctrl) (PV_W5_F31Child.entered s (parent::parents) a n).store
      (PV_W5_F31Child.parent s (parent::parents) a n) (parent::parents) s.nextActivation n false
      PV_STX2_Source7GlobalClone.value w [] external backend

#print Pre
#print Post
#print axioms fuel
#print axioms outcome
end PV_FN_SLICE_f31
