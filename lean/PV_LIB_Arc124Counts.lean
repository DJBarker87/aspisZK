import PV_LIB_Arc124
import PV_FN_THREAD_f124_Counts
set_option autoImplicit false
noncomputable section
namespace PV_LIB_Arc124Counts
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner R1Z.PV_FXM_ReserveWorld
open PV_FN_THREAD_f124_BoxContract PV_THR2_LibrarySemantics_AtomicUsizeNew
abbrev Input := PV_LIB_Arc124.Input

/-- The graph and numeric facts concern the SAME actual4933/4945 requests.
The existing provider semantics facts are retained by name; no new fact. -/
theorem certified (x : Input PV_RJ4IDB.NativeEvent) (H : Backend PV_RJ4IDB.NativeEvent)
    (resources : Resources) (encode : Encode) (shape : PV_THR2_TypedRepresentation_ArcInner.Shape)
    (pre : PV_FN_THREAD_f124.Pre x) (strongChanges weakChanges : Address → Option Data)
    (atomicStrong : Fact (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      (PV_FN_THREAD_f124_Counters.entry7 x) H x.w strongChanges 1)
    (atomicWeak : ∀ sv, Fact (PV_THR2_OwnInitExactReturnedCases.carrier x.C x.b)
      (PV_FN_THREAD_f124_Counters.entry9 x sv) H (strong x H).world weakChanges 1) :
    (∃ out, PV_FN_THREAD_f124.Reached x H resources encode shape out ∧
      PV_LIB_Arc124.law x H resources encode shape (PV_LIB.observe out)) ∧
    PV_FN_THREAD_f124.CountsPost x H resources encode shape :=
  ⟨PV_LIB_Arc124.installed x H resources encode shape pre,
   PV_FN_THREAD_f124.counts x H resources encode shape pre
    (PV_FN_THREAD_f124.contract x H resources encode shape pre)
    strongChanges weakChanges atomicStrong atomicWeak⟩
#print axioms certified
end PV_LIB_Arc124Counts
