import PV_FN_THREAD_f121Value
import PV_THR2_IntrinsicSemantics_NonNullFrom217
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f124Consumer
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
/-- thread-17 consumer interface. Payload is universally quantified: this is
shared by ScopeData in f6 and Packet in f361. No caller-selected layout,
value or receiver is fixed in Pre. Global is fixed by f124's own source. -/
structure Returned (s : Store Data) (caller destination : Nat)
    (payload result : Data) where
  inner : Address
  rootPath : inner.fields = []
  nonNull : Data
  strong : Data
  weak : Data
  returnedValue : result = PV_THR2_Packet124ReturnData.value nonNull
  callerValue : s.cells ⟨caller,destination,[]⟩ = some result
  pointer : nonNull = PV_THR2_IntrinsicSemantics_NonNullFrom217.value
    (PV_STX2_TypedReferences.reference inner .null)
  initialized : s.cells {inner with fields := []} =
    some (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1
      [strong,weak,payload])
  strongOne : PV_THR2_LibrarySemantics_AtomicUsizeNew.Holds strong 1
  weakOne : PV_THR2_LibrarySemantics_AtomicUsizeNew.Holds weak 1

/-- Every answer keeps its actual reply and explicit final store. Freshness
comes from allocation in the callee, rather than an alias premise at clone. -/
def Post {E : Type} (e : PV_W1_LeafBoundary.Entry) (w : OWNER)
    (payload : Data) (r : Reply OWNER E Data) (s : Store Data) : Prop :=
  PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed r.world s.nextActivation ∧
  e.store.nextActivation ≤ s.nextActivation ∧
  (∀ p : Address, p.activation < e.store.nextActivation →
    p ≠ ⟨e.caller,e.destination,[]⟩ → s.cells p = e.store.cells p) ∧
  (∀ result, r.answer = .returned (.ok result) →
    ∃ ret : Returned s e.caller e.destination payload result,
      e.store.nextActivation ≤ ret.inner.activation)

/-- Named pending provider obligation on its actual executed body. The
execution parameter must be the provider's body result, with final store;
this does not identify it with an arbitrary reply on the original store. -/
def Contract {E : Type}
    (execute : PV_W1_LeafBoundary.Entry → OWNER → Reply OWNER E Data × Store Data) : Prop :=
  ∀ (e : PV_W1_LeafBoundary.Entry) (w : OWNER) (payload : Data),
    PV_THR2_OffPath.functionId e.callee = some 124 →
    e.arguments = [payload] →
    PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed w e.store.nextActivation →
    e.caller < e.store.nextActivation →
    let out := execute e w
    Post e w payload out.1 out.2

/-- Both counters' numeric laws follow from the retained121 value contracts. -/
theorem counters (C : Carrier OWNER Data) (b : Bool) (s : Store Data)
    (a dest : Nat) (payload result : Data) (ret : Returned s a dest payload result) :
    readAddress (PV_THR2_OwnInitExactReturnedCases.carrier C b) s
      (PV_THR2_LibrarySemantics_ArcClone.countAddress ret.inner) = some (.number 1) ∧
    readAddress (PV_THR2_OwnInitExactReturnedCases.carrier C b) s
      {ret.inner with fields := ret.inner.fields ++ [1,0,0]} = some (.number 1) := by
  rcases ret.strongOne with ⟨ak,uk,strong⟩
  rcases ret.weakOne with ⟨ak',uk',weak⟩
  have initialized := ret.initialized
  rw [strong,weak] at initialized
  unfold readAddress PV_THR2_LibrarySemantics_ArcClone.countAddress
  rw [ret.rootPath]
  change (_ >>= fun v => readFields _ [0,0,0] v) = _ ∧
    (_ >>= fun v => readFields _ [1,0,0] v) = _
  rw [initialized]
  exact ⟨rfl,rfl⟩
#print axioms counters
end PV_FN_THREAD_f124Consumer
