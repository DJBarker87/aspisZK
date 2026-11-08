import PV_LIB_SPEC_CallbackModelHistory
import PV_LIB_SPEC_SiteArcRecheck
import PV_THR2_TypedRepresentation_Thread
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ThreadRepresentationGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_LIB_SPEC_ScopeAllocationGap PV_LIB_SPEC_SiteArcRecheck

/-- The installed ScopeData codec expects source Thread/Pin/Arc/NonNull
wrappers, whereas the retained Thread native-value facet supplies a word.
This holds for EVERY word, not just a chosen missing header or zero pointer. -/
theorem thread_word (w : OWNER) (word : PV_OWN2_Codec.Pointer) :
    PV_LIB_SPEC_SiteArc.threadWord C w (PV_THR2_OwnInitPointerCodec.encode word) = none := rfl

/-- Exact incompatibility with the named Thread.Shape interface. Its original
Recount14 source/native obligation remains UNPROVED; we do not promote that
hypothesis to a fact about a reached original-entry state. -/
theorem shaped_thread (w : OWNER) (thread : Data)
    (shaped : PV_THR2_TypedRepresentation_Thread.Shape thread) :
    PV_LIB_SPEC_SiteArc.threadWord C w thread = none := by
  obtain ⟨word,rfl⟩ := shaped
  exact thread_word w word

/-- With the source-correct40-byte success, this handler still cannot accept
ANY Thread satisfying its existing native-value facet. ALL other source
fields are their exact intended initial values; no header or image is chosen. -/
theorem scope_handler (encode : Encode) (s : Store Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (w : OWNER) (thread atomicKind cellKind : Data)
    (shaped : PV_THR2_TypedRepresentation_Thread.Shape thread) :
    PV_LIB_SPEC_SiteArc.handler C K PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s H
      (PV_LIB_SPEC_ScopeAllocationPollGap.request s thread (panic atomicKind cellKind)) w = none := by
  rw [PV_LIB_SPEC_SiteArcRecheck.scope_handler,shaped_thread w thread shaped]
  rfl

/-- The two LOCAL interface obligations cannot be jointly inhabited. The
ScopeData request here is not asserted reachable from the original entry.
This is NOT a negation of Cut92Composition.Witness or a security theorem. -/
theorem incompatible (encode : Encode) (s : Store Data)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (w : OWNER) (atomicKind cellKind : Data) :
    ¬ ∃ thread reply,
      PV_THR2_TypedRepresentation_Thread.Shape thread ∧
      PV_LIB_SPEC_SiteArc.handler C K PV_LIB_SPEC_ScopeAllocationPollGap.scopeResources encode s H
        (PV_LIB_SPEC_ScopeAllocationPollGap.request s thread (panic atomicKind cellKind)) w = some reply := by
  rintro ⟨thread,reply,shape,result⟩
  rw [scope_handler encode s H w thread atomicKind cellKind shape] at result
  cases result

#print axioms thread_word
#print axioms shaped_thread
#print axioms scope_handler
#print axioms incompatible
end PV_LIB_SPEC_ThreadRepresentationGap
