import PV_LIB_A_DestructorValues10
import PV_LIB_A_WeakFreeFacts9
import PV_LIB_A_WeakFreeAgreement9
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WeakOwnerFree10
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- Reuse the source interpreter's EXISTING missing-aggregate completion at
native destructor boundaries too. No emitted body or old proved step is edited. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState) : SourceState :=
  PV_LIB_A_WeakOwnerFree9.step (PV_THR2_AggregateCompletion.carrier C) K P resources encode H values s

/-- On the original entry carrier the old native poll cannot reach the free
resource, even when allocator and source backing are available. -/
theorem original_poll_gap (C : Carrier OWNER Data) (b : Bool)
    (resources : Resources) (encode : Encode) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (p : Address) :
    PV_LIB_A_WeakOwnerFree9.poll (PV_THR2_OwnInitExactReturnedCases.carrier C b)
      resources encode c w es stack site p = PV_LIB_A_WeakOwnerFree9.gap c w es stack := by
  unfold PV_LIB_A_WeakOwnerFree9.poll
  rw [PV_LIB_A_DestructorValues10.original_unit_missing]
  cases PV_LIB_A_WeakOwnerFree9.weakAllocator
    (PV_THR2_OwnInitExactReturnedCases.carrier C b) c w site <;> rfl

/-- The value completion does not change source reads, writes, pointer metadata
or native reply selection; it interprets only missing aggregate values. -/
theorem source_fields (C : Carrier OWNER Data) :
    (PV_THR2_AggregateCompletion.carrier C).dereference = C.dereference ∧
    (PV_THR2_AggregateCompletion.carrier C).reference = C.reference ∧
    (PV_THR2_AggregateCompletion.carrier C).field = C.field ∧
    (PV_THR2_AggregateCompletion.carrier C).replaceField = C.replaceField ∧
    (PV_THR2_AggregateCompletion.carrier C).constant = C.constant :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Retained phases still call the same free primitive, without re-decrementing.
The completed carrier is supplied explicitly, rather than assuming unit exists. -/
theorem retry (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (p : Address) (weak : site.action = .weakDrop683) :
    step C K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,some (site,.deallocate p)⟩ =
      PV_LIB_A_WeakOwnerFree9.poll
        (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K)
        resources encode c w es stack site p :=
  PV_LIB_A_WeakOwnerFree9.retry _ _ _ _ _ _ _ _ _ _ _ _ _ weak

#print axioms step
#print axioms original_poll_gap
#print axioms source_fields
#print axioms retry
end PV_LIB_A_WeakOwnerFree10
