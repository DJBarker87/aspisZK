import PV_FN_THREAD_f289_Contract
import PV_FN_THREAD_f207_Contract
set_option autoImplicit false
noncomputable section
namespace PV_FN_W4_ReplaceEffects
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_W1_LeafBoundary PV_W1_OwnerNativeFrame

/-- Native289 entry selected by generated f207/8248. The stored argument
list is fixed before the arbitrary reachable native changes are delivered. -/
def entry (s : Store Data) (a : Nat) (p : Address) (parents : List Frame) : Entry :=
  ⟨PV_FN_THREAD_f207.prepared s a p,a,parents,[],PV_THR2_F207.live.body.drop 6,
    PV_FN_THREAD_f207.fn289,PV_FN_THREAD_f207.args p,0,[]⟩

def changed (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (p : Address) (parents : List Frame) (w : OWNER) (changes : Address → Option Data) : Entry :=
  PV_W1_ArgumentEffects.afterEffects C (entry s a p parents) w changes

/-- The actual Cell argument is writable under the source carrier. In
particular the native adapter cannot silently collapse replace to a pure get. -/
theorem writableCell (base : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (p : Address) (parents : List Frame) (w : OWNER) (b : Bool) :
    PV_W1_ArgumentEffects.Writable (PV_FN_THREAD_f164.carrier base b)
      (entry s a p parents) w {p with fields := []} := by
  refine ⟨PV_STX2_TypedReferences.reference p .null,p,?_,?_,rfl⟩
  · apply PV_W1_ArgumentEffects.Reachable.argument
    simp [entry,PV_FN_THREAD_f207.args]
  · exact PV_STX2_TypedReferences.dereference _ w p .null

theorem changedCell (base : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (p : Address) (parents : List Frame) (w : OWNER) (b : Bool)
    (changes : Address → Option Data) :
    (changed (PV_FN_THREAD_f164.carrier base b) s a p parents w changes).store.cells
      {p with fields := []} = changes {p with fields := []} := by
  classical
  exact if_pos (writableCell base s a p parents w b)

/-- The source's local-only preparation leaves the activation counter intact;
W1's slice-9 native Pre is therefore derived directly from the caller invariant. -/
theorem pre289 (s : Store Data) (a : Nat) (p : Address) (parents : List Frame) (w : OWNER)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    PV_FN_THREAD_f289.Pre (entry s a p parents) w := wf

/-- Actual closed289 contract with explicit changes, at generated8248.
Neither a no-write assumption nor a native ghost-frame hypothesis is used. -/
theorem native {E : Type} (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (p : Address) (parents : List Frame) (H : Backend E) (w : OWNER) (es : List E)
    (changes : Address → Option Data)
    (wf : PV_W1_OwnerWellFormed.OwnerWellFormed w s.nextActivation) :
    PV_FN_THREAD_f289.Post C (entry s a p parents) H w (PV_FN_THREAD_f207.args p) es changes :=
  PV_FN_THREAD_f289.closed C (entry s a p parents) H w (PV_FN_THREAD_f207.args p) es changes
    (pre289 s a p parents w wf)

/-- Native return administration uses the changed Store, not the source store
saved before8248. The reply still comes from the OWNER lift on every branch. -/
def received {E : Type} (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (p : Address) (parents : List Frame) (H : Backend E) (w : OWNER) (es : List E)
    (changes : Address → Option Data) :=
  let d := changed C s a p parents w changes
  deliver C d (PV_THR2_OwnUniformResourceHandler.lift H
    (.child PV_FN_THREAD_f207.fn289 s.nextActivation (PV_FN_THREAD_f207.args p)) w) es

def finalStore (C : Carrier OWNER Data) (s : Store Data) (a dest : Nat)
    (p : Address) (parent : Frame) (parents : List Frame) (w : OWNER)
    (changes : Address → Option Data) (value : Data) : Store Data :=
  let d := changed C s a p (parent :: parents) w changes
  let t := PV_THR2_StaticReply.returnedStore d.store a (PV_FN_THREAD_f207.args p) 0 value
  write (write (PV_FN_THREAD_f207.cleaned t a) ⟨a,0,[]⟩ (some value))
    ⟨parent.activation,dest,[]⟩ (some value)

/-- The successful native branch continues the GENERATED callback suffix on
its explicit final Store. This joins native caller-cell effects to source
cleanup/return without an inline-equals-child store substitution. -/
theorem returned {E : Type} (base : Carrier OWNER Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a dest : Nat) (p : Address) (parent : Frame) (parents : List Frame)
    (wait : PV_STX2_Native.Waiting Data) (H : Backend E) (w : OWNER) (es : List E)
    (changes : Address → Option Data) (value : Data) (b : Bool)
    (answer : (PV_THR2_OwnUniformResourceHandler.lift H
      (.child PV_FN_THREAD_f207.fn289 s.nextActivation (PV_FN_THREAD_f207.args p)) w).answer =
      .returned (.ok value))
    (saved : parent.waiting = some wait) (action : wait.action = .child a (.local dest)) :
    let C := PV_FN_THREAD_f164.carrier base b
    let r := PV_THR2_OwnUniformResourceHandler.lift H
      (.child PV_FN_THREAD_f207.fn289 s.nextActivation (PV_FN_THREAD_f207.args p)) w
    PV_THR2_Execution.advance C ctl programs (PV_THR2_OwnUniformResourceHandler.lift H) 6
      (received C s a p (parent :: parents) H w es changes).current =
    ⟨.running ⟨{parent with waiting := none},parents,
      finalStore C s a dest p parent parents w changes value⟩,r.world,es ++ r.events⟩ := by
  dsimp only
  have delivered := PV_THR2_FrameFullReturned.received
    (PV_FN_THREAD_f164.carrier base b)
    (changed (PV_FN_THREAD_f164.carrier base b) s a p (parent :: parents) w changes).store
    a (parent :: parents) [] (PV_THR2_F207.live.body.drop 6)
    PV_FN_THREAD_f207.fn289 (PV_FN_THREAD_f207.args p) 0 value
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child PV_FN_THREAD_f207.fn289 s.nextActivation (PV_FN_THREAD_f207.args p)) w).world es
    (PV_THR2_OwnUniformResourceHandler.lift H
      (.child PV_FN_THREAD_f207.fn289 s.nextActivation (PV_FN_THREAD_f207.args p)) w).events []
  unfold received PV_W1_LeafBoundary.deliver
  rw [PV_THR2_RunEntryReturned.returned_eta _ value answer]
  dsimp only [changed,PV_W1_ArgumentEffects.afterEffects,entry] at delivered ⊢
  rw [delivered]
  exact PV_FN_THREAD_f207.suffix _ ctl programs _ _ a dest parent parents wait value _ _
    (by simp only [PV_THR2_StaticReply.returnedStore,write_same]) saved action
#print axioms writableCell
#print axioms changedCell
#print axioms pre289
#print axioms native
#print axioms returned
end PV_FN_W4_ReplaceEffects
