import PV_FN_THREAD_f361After124
import PV_FN_THREAD_W3CalleeContracts
import PV_FN_THREAD_NonreturnFrontier
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361MetadataEffects
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
/-- Operand-issued input at one of f361's two metadata LEAF boundaries.
The store includes the actual move invalidation, before argument issuance. -/
structure Input (E : Type) where
  B : Carrier OWNER Data
  K : Control
  P : Data → Option PV_STX2_SliceSyntax.Program
  H : PV_W1_OwnerNativeFrame.Backend E
  s : Store Data
  a : Nat
  parents : List Frame
  loops : List LoopFrame
  vs : List Data
  changes : Address → Option Data
  w : OWNER
  es : List E
  stack : List Config
/-- Actual source12950 descriptor, including its Packet instantiation. -/
def entry360 {E : Type} (x : Input E) : PV_W1_LeafBoundary.Entry :=
  ⟨x.s,x.a,x.parents,x.loops,PV_THR2_F361.live.body.drop 64,
    PV_THR2_Source361PacketChildren.fn63,x.vs,23,x.stack⟩
/-- Actual source13123 descriptor and source continuation. -/
def entry456 {E : Type} (x : Input E) : PV_W1_LeafBoundary.Entry :=
  ⟨x.s,x.a,x.parents,x.loops,PV_THR2_F361.live.body.drop 71,
    PV_THR2_Source361PacketChildren.fn70,x.vs,25,x.stack⟩
def effects {E : Type} (x : Input E) (e : PV_W1_LeafBoundary.Entry) :=
  PV_W1_ArgumentEffects.afterEffects x.B e x.w x.changes
def reply {E : Type} (x : Input E) (e : PV_W1_LeafBoundary.Entry) :=
  PV_THR2_OwnUniformResourceHandler.lift x.H
    (.child e.callee e.store.nextActivation e.arguments) x.w
def delivered {E : Type} (x : Input E) (e : PV_W1_LeafBoundary.Entry) :=
  PV_W1_LeafBoundary.deliver x.B (effects x e) (reply x e) x.es
/-- Instantiate W1's descriptor-parametric full-reply theorem at source12950.
The named f360 wrapper fixes the f270 instantiation, so it cannot be used by
identifying function IDs: generic metadata and pending requests differ. -/
theorem callee360 {E : Type} (x : Input E)
    (pre : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    PV_W1_ArgumentEffects.Post x.B (entry360 x) x.H x.w x.es x.changes :=
  PV_W1_ArgumentEffects.full_reply x.B (entry360 x) x.H x.w x.es x.changes
    (PV_FN_THREAD_W3CalleeContracts.invariant _ _ pre)
/-- The CLOSED456 contract is applied at its exact emitted instantiation. -/
theorem callee456 {E : Type} (x : Input E)
    (pre : PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed x.w x.s.nextActivation) :
    PV_W1_NativeLeaves.Post456 x.B (entry456 x) x.H x.w x.vs x.es x.changes :=
  PV_W1_NativeLeaves.f456 x.B (entry456 x) x.H x.w x.vs x.es x.changes
    (PV_FN_THREAD_W3CalleeContracts.invariant _ _ pre)
/-- No native write is lost: the following source chain is instantiated on
ArgumentEffects.finalStore before reply administration, for every answer. -/
theorem continue360 {E : Type} (x : Input E) :
    ∃ n, PV_THR2_IntrinsicState.advance x.B x.K x.P
      (PV_THR2_OwnUniformResourceHandler.lift x.H) n (delivered x (entry360 x)) =
      PV_THR2_Source361Chain64To70.after x.B (delivered x (entry360 x)) :=
  ⟨PV_THR2_Source361Chain64To70.steps x.B _,PV_THR2_Source361Chain64To70.run _ _ _ _ _⟩
theorem continue456 {E : Type} (x : Input E) :
    ∃ n, PV_THR2_IntrinsicState.advance x.B x.K x.P
      (PV_THR2_OwnUniformResourceHandler.lift x.H) n (delivered x (entry456 x)) =
      PV_THR2_Source361Chain71To76.after x.B (delivered x (entry456 x)) :=
  ⟨PV_THR2_Source361Chain71To76.steps x.B _,PV_THR2_Source361Chain71To76.run _ _ _ _ _⟩
/-- Failure, divergence and pending keep their exact native frontier, complete
modified store, backend post-world, and event suffix. -/
theorem frozen {E : Type} (x : Input E) (e : PV_W1_LeafBoundary.Entry)
    (other : ∀ v, (reply x e).answer ≠ .returned (.ok v)) :
    PV_FN_THREAD_NonreturnFrontier.Frozen (delivered x e) :=
  PV_FN_THREAD_NonreturnFrontier.received x.B (effects x e).store e.caller e.parents
    e.loops e.rest e.callee e.arguments e.destination (reply x e) x.es e.suspended other

theorem other360 {E : Type} (x : Input E)
    (other : ∀ v, (reply x (entry360 x)).answer ≠ .returned (.ok v)) :
    PV_THR2_Source361Chain64To70.after x.B (delivered x (entry360 x)) =
      delivered x (entry360 x) :=
  PV_FN_THREAD_NonreturnFrontier.after _ _ _ (frozen x _ other)
theorem other456 {E : Type} (x : Input E)
    (other : ∀ v, (reply x (entry456 x)).answer ≠ .returned (.ok v)) :
    PV_THR2_Source361Chain71To76.after x.B (delivered x (entry456 x)) =
      delivered x (entry456 x) :=
  PV_FN_THREAD_NonreturnFrontier.after _ _ _ (frozen x _ other)
#print axioms callee360
#print axioms callee456
#print axioms continue360
#print axioms continue456
#print axioms frozen
#print axioms other360
#print axioms other456
end PV_FN_THREAD_f361MetadataEffects
