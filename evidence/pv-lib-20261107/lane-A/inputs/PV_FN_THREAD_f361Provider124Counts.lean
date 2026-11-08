import PV_FN_THREAD_f361Provider124
import PV_FN_THREAD_f121Value
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361Provider124Counts
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_FN_THREAD_f124_BoxContract
/-- Only thread19 documented semantics at the provider's ACTUAL4933/4945
entries. The second fact is used only after the actual first returned case.
No counter-value, root, alias, decoder-success or BODY-output assumption. -/
structure DocumentedFacts (x : Input PV_RJ4IDB.NativeEvent)
    (H : Backend PV_RJ4IDB.NativeEvent) : Prop where
  atomic4933 : PV_THR2_LibrarySemantics_AtomicUsizeNew.Fact
    (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
    (PV_FN_THREAD_f124_Counters.entry7 x) H x.w (fun _ => none) 1
  atomic4945 : ∀ sv, (strong x H).answer = .returned (.ok sv) →
    PV_THR2_LibrarySemantics_AtomicUsizeNew.Fact
      (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      (PV_FN_THREAD_f124_Counters.entry9 x sv) H (strong x H).world (fun _ => none) 1

/-- Instantiate CLOSED121's strengthened law at the actual first request.
The provider's own request and representation definitions are reused. -/
theorem strong_value (x : Input PV_RJ4IDB.NativeEvent)
    (H : Backend PV_RJ4IDB.NativeEvent) (pre : PV_FN_THREAD_f124.Pre x)
    (facts : DocumentedFacts x H) (sv : Data)
    (answer : (strong x H).answer = .returned (.ok sv)) :
    PV_THR2_LibrarySemantics_AtomicUsizeNew.Holds sv 1 := by
  have law := PV_FN_THREAD_f121.contract_value
    (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
    (PV_FN_THREAD_f124_Counters.entry7 x) H x.w x.es (fun _ => none) 1
    pre.owner facts.atomic4933
  exact (law.2.2 sv answer).value

/-- The second actual request has the first reply's full post-world and the
provider's beforeWeak store. Ghost framing discharges its invariant. -/
theorem weak_value (x : Input PV_RJ4IDB.NativeEvent)
    (H : Backend PV_RJ4IDB.NativeEvent) (pre : PV_FN_THREAD_f124.Pre x)
    (facts : DocumentedFacts x H) (sv wv : Data)
    (sa : (strong x H).answer = .returned (.ok sv))
    (wa : (weak x H).answer = .returned (.ok wv)) :
    PV_THR2_LibrarySemantics_AtomicUsizeNew.Holds wv 1 := by
  have framed := PV_W1_OwnerNativeFrame.lift_preserves H
    (.child PV_THR2_Packet124Children.fn7 x.s.nextActivation [.number 1])
    x.w x.s.nextActivation pre.owner
  have owner : PV_W1_ClosedLeaves.Pre (PV_FN_THREAD_f124_Counters.entry9 x sv)
      (strong x H).world :=
    PV_W1_OwnerWellFormed.counter_mono _ _ _ framed (Nat.le_succ _)
  have law := PV_FN_THREAD_f121.contract_value
    (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
    (PV_FN_THREAD_f124_Counters.entry9 x sv) H (strong x H).world
    (x.es ++ (strong x H).events) (fun _ => none) 1 owner (facts.atomic4945 sv sa)
  exact (law.2.2 wv wa).value

/-- Direct strengthening of the EXACT provider statement, not the retired
consumer Contract. Every provider failure/pending branch and complete output
store remains in Post. The numeric equalities follow from contract_value. -/
theorem provider (f124 : PV_FN_THREAD_f361Provider124.Dependency)
    (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (pre : PV_FN_THREAD_f124.Pre x) (facts : DocumentedFacts x H) :
    PV_FN_THREAD_f124.Post x H resources encode shape ∧
    (∀ sv, (strong x H).answer = .returned (.ok sv) →
      PV_THR2_LibrarySemantics_AtomicUsizeNew.Holds sv 1 ∧
      ∀ wv, (weak x H).answer = .returned (.ok wv) →
        PV_THR2_LibrarySemantics_AtomicUsizeNew.Holds wv 1) := by
  refine ⟨f124 x H resources encode shape pre,?_⟩
  intro sv sa
  exact ⟨strong_value x H pre facts sv sa,fun wv wa => weak_value x H pre facts sv wv sa wa⟩

/-- Connect both121 value laws to the provider's ACTUAL COMPLETE return store.
The source root is obtained from Successful's ReturnedPost, never re-derived
from a consumer Arc representation and never assumed at clone12950. -/
theorem returned_counts (x : Input PV_RJ4IDB.NativeEvent)
    (H : Backend PV_RJ4IDB.NativeEvent) (resources : Resources) (encode : Encode)
    (shape : PV_THR2_TypedRepresentation_ArcInner.Shape) (sv wv : Data) (heap : Nat)
    (pre : PV_FN_THREAD_f124.Pre x) (facts : DocumentedFacts x H)
    (sa : (strong x H).answer = .returned (.ok sv))
    (wa : (weak x H).answer = .returned (.ok wv))
    (post : PV_FN_THREAD_f124.Successful x H resources encode shape sv wv heap) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b
    let s := PV_FN_THREAD_f124_ReturnedPost.store x sv wv
    let p := PV_FN_THREAD_f124_StorePost.backing x sv wv
    readAddress B s (PV_THR2_LibrarySemantics_ArcClone.countAddress p) = some (.number 1) ∧
    readAddress B s {p with fields := p.fields ++ [1,0,0]} = some (.number 1) := by
  have initialized := post.2.1.2.1
  have hs := strong_value x H pre facts sv sa
  have hw := weak_value x H pre facts sv wv sa wa
  dsimp only
  unfold readAddress PV_THR2_LibrarySemantics_ArcClone.countAddress
  change ((PV_FN_THREAD_f124_ReturnedPost.store x sv wv).cells
      (PV_FN_THREAD_f124_StorePost.backing x sv wv) >>= fun v =>
        readFields (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) [0,0,0] v) = _ ∧
    ((PV_FN_THREAD_f124_ReturnedPost.store x sv wv).cells
      (PV_FN_THREAD_f124_StorePost.backing x sv wv) >>= fun v =>
        readFields (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) [1,0,0] v) = _
  rw [initialized]
  obtain ⟨ak,uk,rfl⟩ := hs
  obtain ⟨ak',uk',rfl⟩ := hw
  exact ⟨rfl,rfl⟩

#print axioms strong_value
#print axioms weak_value
#print axioms provider
#print axioms returned_counts
end PV_FN_THREAD_f361Provider124Counts
