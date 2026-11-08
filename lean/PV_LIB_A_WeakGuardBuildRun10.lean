import PV_LIB_A_WeakGuardBuild10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakGuardBuildRun10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_WeakGuardBuild10

theorem corrected_step (C : Carrier OWNER Data) (K : Control) (b : Bool)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (types : List Data) (s : Store Data) (a : Nat) (parents : List Frame)
    (root slot : Nat) (ptr : Data) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (older : root ≠ a)
    (source : s.cells ⟨root,slot,[]⟩ = some
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator))
    (n : Nat) (bound : n < 8) :
    PV_LIB_A_WeakOwnerFree10.step (PV_THR2_OwnInitExactReturnedCases.carrier C b) K
      P resources encode H values
      ⟨⟨⟨.running (configuration types s a parents root slot ptr n),w,es⟩,stack⟩,none⟩ =
      ⟨⟨⟨.running (configuration types s a parents root slot ptr (n+1)),w,es⟩,stack⟩,none⟩ := by
  have raw := raw_step C K b (v2ProvenancePrograms P) H types s a parents root slot ptr w older source n bound
  have defined : ∀ site t,
      (PV_STX2_SliceMachine.step
        (PV_LIB_A_UnwindMatch.carrier (PV_LIB_A_DestructorValues10.carrier C b) K) K
        (v2ProvenancePrograms P) H (configuration types s a parents root slot ptr n) w).status ≠
          .undefined site t := by
    rw [raw]
    intro site t bad
    cases bad
  rw [PV_LIB_A_DestructorStep10.ordinary (interpreted := defined)]
  · rw [show PV_STX2_SliceMachine.step
      (PV_LIB_A_UnwindMatch.carrier
        (PV_THR2_AggregateCompletion.carrier (PV_THR2_OwnInitExactReturnedCases.carrier C b)) K)
      K (v2ProvenancePrograms P) H (configuration types s a parents root slot ptr n) w = _ from raw]
    simp only [List.append_nil]
  all_goals
    have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [configuration,PV_LIB_A_TypedBody584.program,
      PV_LIB_A_TypedBody584.block30,PV_LIB_A_TypedBody584.node0,
      PV_LIB_A_TypedBody584.node1,PV_LIB_A_TypedBody584.node2,
      PV_LIB_A_TypedBody584.node3,PV_LIB_A_TypedBody584.node4,
      PV_LIB_A_TypedBody584.node5,PV_LIB_A_TypedBody584.node6,
      PV_LIB_A_TypedBody584.node7,PV_THR2_OwnInitAction.selected,
      PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
      PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction,
      PV_THR2_Dynamic.active,PV_THR2_Dynamic.operandOf]


/-- The guard root and source allocator root are separately retained. -/
theorem source_root (types : List Data) (s : Store Data) (a root slot : Nat)
    (ptr : Data) (older : root ≠ a) :
    (stage types s a root slot ptr 8).cells ⟨root,slot,[]⟩ = s.cells ⟨root,slot,[]⟩ := by
  simp [stage,entry,write,older]

theorem guard_root (types : List Data) (s : Store Data) (a root slot : Nat) (ptr : Data) :
    (stage types s a root slot ptr 8).cells ⟨a,2,[]⟩ = some (guard types ptr root slot) := by
  simp [stage,write]

/-- Allocator validity is DERIVED from the provider's actual Arc aggregate and
584's emitted guard. No allocator value or allocator-read premise is added. -/
theorem allocator (C : Carrier OWNER Data) (b : Bool) (types : List Data)
    (s : Store Data) (w : OWNER) (a root slot : Nat) (ptr : Data)
    (older : root ≠ a)
    (source : s.cells ⟨root,slot,[]⟩ = some
      (PV_THR2_Packet315SourceReturn.value ptr PV_THR2_Packet218ReturnData.allocator)) :
    ∃ value,
      (PV_LIB_A_DestructorValues10.carrier C b).field (guard types ptr root slot) 1 = some value ∧
      PV_LIB_A_WeakOwnerFree9.allocator (PV_LIB_A_DestructorValues10.carrier C b)
        (stage types s a root slot ptr 8) w
        (.object [("Ref",.array [.object [("Body",.number 8)],
          PV_LIB_A_AllocatorProvenance.globalType,.atom "Shared"])]) value = some () := by
  refine ⟨PV_STX2_TypedReferences.reference ⟨root,slot,[2]⟩ .null,rfl,?_⟩
  apply PV_LIB_A_WeakAllocatorFacts9.borrowed (p := ⟨root,slot,[2]⟩)
  · exact PV_LIB_A_DestructorValues10.reference C b _ _ w
  · change ((stage types s a root slot ptr 8).cells ⟨root,slot,[]⟩).bind _ = _
    rw [source_root types s a root slot ptr older,source]
    rfl

#print axioms corrected_step
#print axioms source_root
#print axioms guard_root
#print axioms allocator
end PV_LIB_A_WeakGuardBuildRun10
