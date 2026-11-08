import PV_FN_THREAD_f124
import PV_FN_THREAD_f6InterfaceSites
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f6Provider124Entry
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f6Interfaces
open PV_FN_THREAD_f124_BoxContract PV_EVHB_OwnerHeap

/-- Literally the type of the pinned provider theorem. No consumer Post or
representation replaces the provider's Pre/Post. The row remains PARTIAL. -/
def Contract : Prop :=
  ∀ (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape),
    PV_FN_THREAD_f124.Pre x → PV_FN_THREAD_f124.Post x H resources encode shape

theorem exact_provider_type : Contract := PV_FN_THREAD_f124.contract

/-- The actual1916 argument is source ScopeData, with its emitted shape. -/
def convert (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend PV_RJ4IDB.NativeEvent)
    (x : Entry PV_RJ4IDB.NativeEvent) (payload : Data) : Input PV_RJ4IDB.NativeEvent :=
  {C := C,b := b,K := K,P := P,H := PV_THR2_OwnUniformResourceHandler.lift H,
   s := x.store,a := x.activation,dest := x.dest,parent := x.parent,
   parents := x.parents,wait := x.wait,ptr := payload,allocator := .null,
   w := x.world,es := x.events,stack := x.suspended}

theorem same_entry (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend PV_RJ4IDB.NativeEvent)
    (x : Entry PV_RJ4IDB.NativeEvent) (payload : Data) (body : x.body = PV_THR2_F124.live) :
    PV_FN_THREAD_f124_Arbitrary.entry (convert C b K P H x payload) = PV_FN_THREAD_f6Interfaces.entry x := by
  simp only [PV_FN_THREAD_f124_Arbitrary.entry,convert,PV_FN_THREAD_f6Interfaces.entry,body]

/-- Internal live-stack invariant. The full f6 composition must derive these
bounds from its original call entry; they are not endpoint hypotheses. -/
def StackBounded {E : Type} (x : Entry E) : Prop :=
  (∀ f ∈ x.parents, f.activation < x.store.nextActivation) ∧
  (∀ c ∈ x.suspended, ∀ f ∈ c.frame :: c.callers, f.activation < x.store.nextActivation)

theorem pre (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend PV_RJ4IDB.NativeEvent)
    (x : Entry PV_RJ4IDB.NativeEvent) (payload : Data)
    (valid : EntryValid x) (args : x.args = [payload]) (bounds : StackBounded x) :
    PV_FN_THREAD_f124.Pre (convert C b K P H x payload) := by
  rcases valid with ⟨counter,parent,saved,action,request,owner,arguments⟩
  refine ⟨⟨?_,?_⟩,saved,action,?_,bounds.2,?_⟩
  · exact arguments 0 payload (by rw [args]; rfl)
  · change x.activation < x.store.nextActivation
    omega
  · intro f member
    rcases List.mem_cons.mp member with h | h
    · subst f
      change x.parent.activation < x.store.nextActivation
      omega
    · exact bounds.1 f h
  · exact PV_W1_OwnerWellFormed.counter_mono x.world x.activation x.store.nextActivation
      owner (by omega)

/-- f6's own constructor prefix increases the counter by four, including
issuance of124, and leaves both lower stacks intact. -/
theorem arc_bounds {E : Type} (s : Store Data) (a : Nat) (parents : List Frame)
    (counter thread panicked : Data) (w : OWNER) (es : List E) (stack : List Config)
    (callers : ∀ f ∈ parents, f.activation < s.nextActivation)
    (suspended : ∀ c ∈ stack, ∀ f ∈ c.frame :: c.callers, f.activation < s.nextActivation) :
    StackBounded (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack) := by
  constructor
  · intro f member
    change f.activation < s.nextActivation+4
    exact Nat.lt_of_lt_of_le (callers f member) (Nat.le_add_right _ _)
  · intro c member f frame
    change f.activation < s.nextActivation+4
    exact Nat.lt_of_lt_of_le (suspended c member f frame) (Nat.le_add_right _ _)

/-- The exact provider contract is a named dependency argument at1916.
The bound hypotheses are intermediate caller-invariant projections. -/
theorem at1916 (thread_f124 : Contract)
    (C : Carrier OWNER Data) (b : Bool) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (s : Store Data) (a : Nat) (parents : List Frame) (counter thread panicked : Data)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (live : a < s.nextActivation) (owner : OwnerWellFormed w (s.nextActivation+3))
    (bounds : StackBounded (PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack)) :
    let x := PV_FN_THREAD_f6InterfaceSites.arcInput s a parents counter thread panicked w es stack
    PV_FN_THREAD_f124.Post (convert C b K P H x (PV_THR2_ScopeData.value counter thread panicked))
      H resources encode shape := by
  apply thread_f124 _ H resources encode shape
  apply pre
  · exact PV_FN_THREAD_f6InterfaceSites.arc_valid s a parents counter thread panicked w es stack live owner
  · rfl
  · exact bounds

#print axioms exact_provider_type
#print axioms same_entry
#print axioms pre
#print axioms arc_bounds
#print axioms at1916
end PV_FN_THREAD_f6Provider124Entry
