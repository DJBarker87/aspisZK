import PV_LIB_A_Caller124
import PV_LIB_A_ArcStoreV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CloneValidityV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_FN_THREAD_f124_BoxContract
/-- Actual12802/12803/12804/12805 and the operand move at12950.
No native operation occurs between constructor return and this issued store. -/
def prepare (s : Store Data) (a : Nat) : Store Data :=
  write (write (write (write (write s ⟨a,18,[]⟩ none) ⟨a,23,[]⟩ none)
    ⟨a,24,[]⟩ none) ⟨a,24,[]⟩
      (some (PV_STX2_TypedReferences.reference ⟨a,17,[]⟩ .null))) ⟨a,24,[]⟩ none

def cloneEntry (x : Input PV_RJ4IDB.NativeEvent) (sv wv : Data) : PV_W1_LeafBoundary.Entry :=
  ⟨prepare (PV_FN_THREAD_f124_ReturnedPost.store x sv wv) x.parent.activation,
    x.parent.activation,x.parents,[],PV_THR2_F361.live.body.drop 64,
    PV_THR2_Source361PacketChildren.fn63,
    [PV_STX2_TypedReferences.reference ⟨x.parent.activation,17,[]⟩ .null],23,x.stack⟩

theorem caller17 (s : Store Data) (a : Nat) :
    (prepare s a).cells ⟨a,17,[]⟩ = s.cells ⟨a,17,[]⟩ := by
  simp [prepare,write]

theorem foreign (s : Store Data) (a : Nat) (p : Address) (other : p.activation ≠ a) :
    (prepare s a).cells p = s.cells p := by
  have different (i : Nat) : p ≠ (⟨a,i,[]⟩ : Address) :=
    fun eq => other (congrArg Address.activation eq)
  simp only [prepare,write_other _ _ _ _ (different 24),
    write_other _ _ _ _ (different 23),write_other _ _ _ _ (different 18)]

theorem read_foreign (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (p : Address) (other : p.activation ≠ a) :
    readAddress C (prepare s a) p = readAddress C s p := by
  unfold readAddress
  rw [foreign s a {p with fields := []} other]

/-- Derive ArcClone.Valid from CLOSED124's SAME successful return store and
its existing AtomicUsize::new facts, then preserve the cells through the source
prologue. No Valid/nonzero/count/root/alias premise is added at clone12950.
The selected constructor entry and corrected-machine predecessor history still
belong to the caller composition; this theorem does not assert that reachability. -/
def from124 (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (sv wv : Data) (heap : Nat) (w : OWNER)
    (pre : PV_FN_THREAD_f124.Pre x)
    (facts : PV_FN_THREAD_f361Provider124Counts.DocumentedFacts x H)
    (destination : x.dest = 17)
    (sa : (strong x H).answer = .returned (.ok sv))
    (wa : (weak x H).answer = .returned (.ok wv))
    (post : PV_FN_THREAD_f124.Successful x H resources encode shape sv wv heap) :
    PV_THR2_LibrarySemantics_ArcClone.Valid
      (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) (cloneEntry x sv wv) w := by
  let B := PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b
  let s := PV_FN_THREAD_f124_ReturnedPost.store x sv wv
  let p := PV_FN_THREAD_f124_StorePost.backing x sv wv
  have parentAge := pre.callers x.parent (List.mem_cons_self)
  have notCaller : p.activation ≠ x.parent.activation := by
    change x.s.nextActivation+2 ≠ x.parent.activation
    omega
  have counts := PV_FN_THREAD_f361Provider124Counts.returned_counts
    x H resources encode shape sv wv heap pre facts sa wa post
  have arcCell : (prepare s x.parent.activation).cells ⟨x.parent.activation,17,[]⟩ =
      some (PV_THR2_Packet124ReturnData.value (PV_FN_THREAD_f124_ReturnedPost.nonNull x sv wv)) := by
    rw [caller17]
    simpa only [destination] using post.2.1.1
  refine {
    arc := ⟨x.parent.activation,17,[]⟩
    inner := p
    nonNull := PV_FN_THREAD_f124_ReturnedPost.nonNull x sv wv
    allocator := PV_THR2_Packet218ReturnData.allocator
    count := 1
    function := by rfl
    arguments := by rfl
    arcRoot := ?_
    innerPointer := by rfl
    initialized := ?_
    strongCount := ?_
    nonzero := by decide
    fits := by decide }
  · change ((prepare s x.parent.activation).cells ⟨x.parent.activation,17,[]⟩).bind _ = _
    rw [arcCell]
    rfl
  · refine ⟨sv,wv,x.ptr,?_⟩
    change readAddress B (prepare s x.parent.activation) p = _
    rw [read_foreign B s x.parent.activation p notCaller]
    change (s.cells p).bind _ = _
    rw [post.2.1.2.1]
    rfl
  · change readAddress B (prepare s x.parent.activation)
      (PV_THR2_LibrarySemantics_ArcClone.countAddress p) = _
    rw [read_foreign B s x.parent.activation
      (PV_THR2_LibrarySemantics_ArcClone.countAddress p) notCaller]
    exact counts.1

#print axioms caller17
#print axioms foreign
#print axioms read_foreign
#print axioms from124
end PV_LIB_A_CloneValidityV2
