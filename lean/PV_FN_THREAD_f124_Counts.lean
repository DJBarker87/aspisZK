import PV_FN_THREAD_f124
import PV_FN_THREAD_f124Consumer
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f124
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_EVHB_OwnerHeap
open PV_FN_THREAD_f124_BoxContract
open PV_THR2_LibrarySemantics_AtomicUsizeNew

/-- D898 strengthens the existing all-answer Post. Both named facts concern
only the actual source4933/4945 requests, with their actual stores/worlds. -/
def CountsPost (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape) : Prop :=
  Post x H resources encode shape ∧
  (∀ sv, (strong x H).answer = .returned (.ok sv) → Holds sv 1) ∧
  (∀ sv wv, (strong x H).answer = .returned (.ok sv) →
    (weak x H).answer = .returned (.ok wv) → Holds wv 1)

theorem counts (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (pre : Pre x) (post : Post x H resources encode shape)
    (strongChanges weakChanges : Address → Option Data)
    (atomicStrong : Fact (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      (PV_FN_THREAD_f124_Counters.entry7 x) H x.w strongChanges 1)
    (atomicWeak : ∀ sv, Fact (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      (PV_FN_THREAD_f124_Counters.entry9 x sv) H (strong x H).world weakChanges 1) :
    CountsPost x H resources encode shape := by
  have first := PV_FN_THREAD_f121.contract_value
    (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
    (PV_FN_THREAD_f124_Counters.entry7 x) H x.w x.es strongChanges 1 pre.owner atomicStrong
  have wf := PV_W1_OwnerNativeFrame.lift_preserves H
    (.child PV_THR2_Packet124Children.fn7 x.s.nextActivation [.number 1]) x.w x.s.nextActivation pre.owner
  refine ⟨post,?_,?_⟩
  · intro sv answer
    exact (first.2.2 sv answer).value
  · intro sv wv strongAnswer weakAnswer
    have second := PV_FN_THREAD_f121.contract_value
      (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      (PV_FN_THREAD_f124_Counters.entry9 x sv) H (strong x H).world
      (x.es ++ (strong x H).events) weakChanges 1
      (PV_W1_OwnerWellFormed.counter_mono _ _ _ wf (Nat.le_succ _)) (atomicWeak sv)
    exact (second.2.2 wv weakAnswer).value

/-- The successful actual body output supplies W3's complete named Post:
initialized Arc, numeric counters, older-cell frame, allocation freshness and
OWNER invariant. No caller payload or representation is specialized. -/
theorem counts_consumer (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (pre : Pre x) (post : CountsPost x H resources encode shape)
    (sv wv : Data) (heap : Nat)
    (sa : (strong x H).answer = .returned (.ok sv))
    (wa : (weak x H).answer = .returned (.ok wv))
    (success : Successful x H resources encode shape sv wv heap) :
    let y := PV_FN_THREAD_f124_ClosedLeak.input x H resources encode shape sv wv
    let e : PV_W1_LeafBoundary.Entry :=
      {store := {x.s with nextActivation := x.a},caller := x.parent.activation,parents := x.parents,loops := x.parent.loops,rest := x.parent.remaining,
       callee := (match x.wait.request with | .child fn _ _ => fn | _ => .null),arguments := [x.ptr],destination := x.dest,suspended := x.stack}
    let r : Reply OWNER PV_RJ4IDB.NativeEvent Data :=
      ⟨.returned (.ok (PV_THR2_Packet124ReturnData.value (PV_FN_THREAD_f124_ReturnedPost.nonNull x sv wv))),y.w,y.es.drop x.es.length⟩
    PV_FN_THREAD_f124Consumer.Post e x.w x.ptr r (PV_FN_THREAD_f124_ReturnedPost.store x sv wv) := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · exact ⟨success.1.2.2.1,success.1.2.2.2⟩
  · change x.a ≤ (PV_FN_THREAD_f124_ReturnedPost.store x sv wv).nextActivation
    rw [success.2.1.2.2.2]
    have age := pre.fresh
    omega
  · intro q older destination
    change q.activation < x.a at older
    exact success.1.2.1 q (by omega) (by intro i bound; have age := pre.fresh; omega) destination
  · intro result answer
    cases answer
    refine ⟨{
      inner := PV_FN_THREAD_f124_StorePost.backing x sv wv
      rootPath := rfl
      nonNull := PV_FN_THREAD_f124_ReturnedPost.nonNull x sv wv
      strong := sv
      weak := wv
      returnedValue := rfl
      callerValue := success.2.1.1
      pointer := rfl
      initialized := success.2.1.2.1
      strongOne := post.2.1 sv sa
      weakOne := post.2.2 sv wv sa wa},?_⟩
    change x.a ≤ x.s.nextActivation+2
    have age := pre.fresh
    omega
#print axioms counts
#print axioms counts_consumer
end PV_FN_THREAD_f124
