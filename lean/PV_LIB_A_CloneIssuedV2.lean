import PV_LIB_A_CloneValidityV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CloneIssuedV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_FN_THREAD_f124_BoxContract

theorem issued_cell (s : Store Data) (argument : Data) (p : Address)
    (older : p.activation ≠ s.nextActivation) :
    (PV_THR2_StaticCall.issued s [argument]).cells p = s.cells p := by
  have different : p ≠ (⟨s.nextActivation,1,[]⟩ : Address) :=
    fun eq => older (congrArg Address.activation eq)
  simp only [PV_THR2_StaticCall.issued,PV_STX2_Native.arguments,write_other _ _ _ _ different]

theorem issued_read (C : Carrier OWNER Data) (s : Store Data) (argument : Data)
    (p : Address) (older : p.activation ≠ s.nextActivation) :
    readAddress C (PV_THR2_StaticCall.issued s [argument]) p = readAddress C s p := by
  unfold readAddress
  rw [issued_cell s argument {p with fields := []} older]

/-- Transport an initialized source Arc through the actual one-argument native
issuance. Only the two existing activation-age invariants are needed; no source
root/count/read or future-write assumption is introduced. -/
def issue_valid (C : Carrier OWNER Data) (e : PV_W1_LeafBoundary.Entry) (w : OWNER)
    (v : PV_THR2_LibrarySemantics_ArcClone.Valid C e w) (argument : Data)
    (arguments : e.arguments = [argument])
    (arcOlder : v.arc.activation ≠ e.store.nextActivation)
    (innerOlder : v.inner.activation ≠ e.store.nextActivation) :
    PV_THR2_LibrarySemantics_ArcClone.Valid C
      {e with store := PV_THR2_StaticCall.issued e.store e.arguments} w := by
  refine {v with arcRoot := ?_,initialized := ?_,strongCount := ?_}
  · rw [arguments,issued_read C e.store argument v.arc arcOlder]
    exact v.arcRoot
  · rcases v.initialized with ⟨strong,weak,packet,root⟩
    refine ⟨strong,weak,packet,?_⟩
    rw [arguments,issued_read C e.store argument v.inner innerOlder]
    exact root
  · rw [arguments,issued_read C e.store argument
      (PV_THR2_LibrarySemantics_ArcClone.countAddress v.inner) innerOlder]
    exact v.strongCount

/-- Derive both age facts from the literal provider's Pre and returned store's
counter formula; do not ask the caller for arbitrary alias/separation facts. -/
def from124 (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (sv wv : Data) (heap : Nat) (w : OWNER)
    (pre : PV_FN_THREAD_f124.Pre x)
    (facts : PV_FN_THREAD_f361Provider124Counts.DocumentedFacts x H)
    (destination : x.dest = 17)
    (sa : (strong x H).answer = .returned (.ok sv))
    (wa : (weak x H).answer = .returned (.ok wv))
    (post : PV_FN_THREAD_f124.Successful x H resources encode shape sv wv heap) :
    let e := PV_LIB_A_CloneValidityV2.cloneEntry x sv wv
    PV_THR2_LibrarySemantics_ArcClone.Valid
      (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      {e with store := PV_THR2_StaticCall.issued e.store e.arguments} w := by
  let v := PV_LIB_A_CloneValidityV2.from124 x H resources encode shape sv wv heap w
    pre facts destination sa wa post
  apply issue_valid _ _ w v
    (PV_STX2_TypedReferences.reference ⟨x.parent.activation,17,[]⟩ .null) rfl
  · change x.parent.activation ≠ x.s.nextActivation+9
    have old := pre.callers x.parent (List.mem_cons_self)
    omega
  · change x.s.nextActivation+2 ≠ x.s.nextActivation+9
    omega

#print axioms issued_cell
#print axioms issued_read
#print axioms issue_valid
#print axioms from124
end PV_LIB_A_CloneIssuedV2
