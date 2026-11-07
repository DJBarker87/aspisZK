import PV_FN_THREAD_f443
import PV_FN_THREAD_f458Closed
import PV_THR2_F361
import PV_W1_NamedLeafBoundary
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361BoxCallees
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Exact operand-issued caller context. No callee instructions are traversed. -/
structure Input (E : Type) where
  C : Carrier OWNER Data
  b : Bool
  K : Control
  P : Data → Option PV_STX2_SliceSyntax.Program
  native : PV_STX2_Native.Request Data → PV_STX_World.World → Reply PV_STX_World.World E Data
  s : Store Data
  a : Nat
  parents : List Frame
  loops : List LoopFrame
  w : OWNER
  es : List E
  stack : List Config

def fn443 := PV_W1_NamedLeafBoundary.function PV_THR2_F361.node127
def fn458 := PV_W1_NamedLeafBoundary.function PV_THR2_F361.node139
def pending443 {E : Type} (x : Input E) (p : Address) :=
  PV_THR2_IntrinsicFrameEnter.pending x.s x.a x.parents x.loops
    (PV_THR2_F361.live.body.drop 95) fn443 [PV_STX2_TypedReferences.reference p .null] 38
def entered443 {E : Type} (x : Input E) (p : Address) :=
  PV_THR2_IntrinsicFrameEnter.entered x.s x.a x.parents x.loops
    (PV_THR2_F361.live.body.drop 95) fn443 [PV_STX2_TypedReferences.reference p .null] 38 PV_THR2_F443.live
def child443 {E : Type} (x : Input E) (p : Address) : PV_FN_THREAD_f443.Input E :=
  {C := x.C,b := x.b,K := x.K,P := x.P,native := x.native,
   s := (entered443 x p).store,a := (entered443 x p).frame.activation,dest := 38,
   parent := (pending443 x p).frame,parents := x.parents,
   wait := PV_THR2_StaticReply.wait x.s fn443 [PV_STX2_TypedReferences.reference p .null] 38,
   ptr := p,w := x.w,es := x.es,stack := x.stack}
/-- The call-entry Pre is derived entirely from source argument issuance and
the minting-boundary OWNER invariant. No saved-action or freshness premise. -/
theorem pre443 {E : Type} (x : Input E) (p : Address)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    PV_FN_THREAD_f443.Pre (child443 x p) := by
  refine ⟨?_,?_,rfl,rfl⟩
  · exact PV_FN_THREAD_OwnerWellFormed.call_entry_pre x.w x.s owner x.a x.parents x.loops
      (PV_THR2_F361.live.body.drop 95) fn443 [PV_STX2_TypedReferences.reference p .null] 38 PV_THR2_F443.live
  · simp [child443,entered443,PV_THR2_IntrinsicFrameEnter.entered,
      PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write]
/-- CLOSED443 is instantiated at14113's actual saved continuation and return
slot. Its Post carries the complete store on every branch. -/
theorem callee443 {E : Type} (x : Input E) (p : Address)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    PV_FN_THREAD_f443.Post (child443 x p) :=
  PV_FN_THREAD_f443.contract (child443 x p) (pre443 x p owner)

def pending458 {E : Type} (x : Input E) (raw : Data) :=
  PV_THR2_IntrinsicFrameEnter.pending x.s x.a x.parents x.loops
    (PV_THR2_F361.live.body.drop 107) fn458 [raw] 37
def entered458 {E : Type} (x : Input E) (raw : Data) :=
  PV_THR2_IntrinsicFrameEnter.entered x.s x.a x.parents x.loops
    (PV_THR2_F361.live.body.drop 107) fn458 [raw] 37 PV_THR2_F458.live
def child458 {E : Type} (x : Input E) (raw : Data) : PV_FN_THREAD_f458Entry.Input E :=
  {C := x.C,b := x.b,K := x.K,P := x.P,native := x.native,
   s := (entered458 x raw).store,a := (entered458 x raw).frame.activation,dest := 37,
   parent := (pending458 x raw).frame,parents := x.parents,
   wait := PV_THR2_StaticReply.wait x.s fn458 [raw] 37,
   raw := raw,w := x.w,es := x.es,stack := x.stack}
theorem pre458 {E : Type} (x : Input E) (raw : Data)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    PV_FN_THREAD_f458Entry.Pre (child458 x raw) := by
  refine ⟨?_,?_,rfl,rfl⟩
  · exact PV_FN_THREAD_OwnerWellFormed.call_entry_pre x.w x.s owner x.a x.parents x.loops
      (PV_THR2_F361.live.body.drop 107) fn458 [raw] 37 PV_THR2_F458.live
  · simp [child458,entered458,PV_THR2_IntrinsicFrameEnter.entered,
      PV_THR2_IntrinsicFrameEnter.pending,PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write]
/-- CLOSED458 consumes the actual fat-pointer payload from14313, uniformly
in its bytes. Its612 primitive fact stays named; no BODY contract is assumed. -/
theorem callee458 {E : Type} (x : Input E) (raw : Data)
    (owner : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation)
    (unique612 : PV_THR2_IntrinsicSemantics_UniqueNewUnchecked612.Fact x.native) :
    PV_FN_THREAD_f458.PostWithPointer (child458 x raw) :=
  PV_FN_THREAD_f458.contract (child458 x raw) (pre458 x raw owner) unique612
#print axioms pre443
#print axioms callee443
#print axioms pre458
#print axioms callee458
end PV_FN_THREAD_f361BoxCallees
