import PV_LIB_A_CloneIssuedV2
import PV_LIB_A_ArcMemoryV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CloneCountV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_FN_THREAD_f124_BoxContract

/-- Starting from the SAME literal CLOSED124 return, source4933/4945 value
facts determine count1. Source prologue plus native argument issuance preserve
its BoxNew cell. The new360 source action then writes count2, preserving the
actual weak value and Packet. No source root/alias/write-definedness or desired
Store is assumed at12950. This is a local branch theorem: actual constructor
entry transport, native return value and full caller history remain separate. -/
theorem from124 (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (sv wv : Data) (heap : Nat) (w : OWNER)
    (pre : PV_FN_THREAD_f124.Pre x)
    (facts : PV_FN_THREAD_f361Provider124Counts.DocumentedFacts x H)
    (destination : x.dest = 17)
    (sa : (strong x H).answer = .returned (.ok sv))
    (wa : (weak x H).answer = .returned (.ok wv))
    (post : PV_FN_THREAD_f124.Successful x H resources encode shape sv wv heap) :
    let e := PV_LIB_A_CloneValidityV2.cloneEntry x sv wv
    let issued := PV_THR2_StaticCall.issued e.store e.arguments
    ∃ ak uk,
      PV_LIB_A_ArcStoreV2.PV_THR2_LibrarySemantics_ArcClone360
        (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b) e.arguments issued w =
        some (write issued (PV_FN_THREAD_f124_StorePost.backing x sv wv)
          (some (PV_LIB_A_ArcMemoryV2.block PV_THR2_Packet124Aggregate13.source.2.2.1
            ak uk 2 wv x.ptr))) := by
  intro e issued
  let B := PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b
  let p := PV_FN_THREAD_f124_StorePost.backing x sv wv
  let v := PV_LIB_A_CloneIssuedV2.from124 x H resources encode shape sv wv heap w
    pre facts destination sa wa post
  have age := pre.callers x.parent (List.mem_cons_self)
  have older : p.activation ≠ e.store.nextActivation := by
    change x.s.nextActivation+2 ≠ x.s.nextActivation+9
    omega
  have foreign : p.activation ≠ x.parent.activation := by
    change x.s.nextActivation+2 ≠ x.parent.activation
    omega
  have cell : issued.cells p =
      some (PV_THR2_KeyValues.pack PV_THR2_Packet124Aggregate13.source.2.2.1 [sv,wv,x.ptr]) := by
    change (PV_THR2_StaticCall.issued e.store
      [PV_STX2_TypedReferences.reference ⟨x.parent.activation,17,[]⟩ .null]).cells p = _
    rw [PV_LIB_A_CloneIssuedV2.issued_cell e.store _ p older]
    change (PV_LIB_A_CloneValidityV2.prepare (PV_FN_THREAD_f124_ReturnedPost.store x sv wv)
      x.parent.activation).cells p = _
    rw [PV_LIB_A_CloneValidityV2.foreign _ _ p foreign]
    exact post.2.1.2.1
  rcases PV_FN_THREAD_f361Provider124Counts.strong_value x H pre facts sv sa with ⟨ak,uk,strongValue⟩
  refine ⟨ak,uk,?_⟩
  have root : issued.cells p = some
      (PV_LIB_A_ArcMemoryV2.block PV_THR2_Packet124Aggregate13.source.2.2.1 ak uk 1 wv x.ptr) := by
    rw [cell,strongValue]
    rfl
  have resolved := PV_LIB_A_ArcStoreV2.valid_inner x.C x.b
    {e with store := issued} w v
  have count : readAddress B issued (PV_THR2_LibrarySemantics_ArcClone.countAddress p) =
      some (.number 1) := v.strongCount
  rw [PV_LIB_A_ArcStoreV2.clone_count B issued w e.arguments p 1 resolved count]
  have two : (1+1)%PV_LIB_A_StorePrimitiveV2.modulus = 2 := by decide
  rw [two]
  exact PV_LIB_A_ArcMemoryV2.write_count x.C x.b issued (x.s.nextActivation+2) 1 1 2
    PV_THR2_Packet124Aggregate13.source.2.2.1 ak uk wv x.ptr root

#print axioms from124
end PV_LIB_A_CloneCountV2
