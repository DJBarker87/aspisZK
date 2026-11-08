import PV_LIB_A_WriterSites
import PV_LIB_A_PurePoll
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_WriterOrdinary
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_W1_LeafBoundary
open PV_LIB_A_OwnerStore PV_THR2_SourceStoreLibrary
/-- Writer dispatch itself excludes the intrinsic catch token. This local
administrative fact is derived from the source token, not a caller premise. -/
theorem noncatch (e : Entry) (f : PV_THR2_SourceStoreNative.Function)
    (meaning : PV_THR2_SourceStoreNative.function e.callee = some f) :
    PV_THR2_Catch316Segment.select (pending e) = none := by
  apply PV_LIB_A_PurePoll.noncatch
  intro equal
  rw [equal] at meaning
  change none = some f at meaning
  cases meaning

/-- Corrected-machine binding with the catch-exclusion obligation discharged.
All full replies and W4's undefined-layout branch remain in the graph. -/
theorem installed (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (e : Entry) (f : PV_THR2_SourceStoreNative.Function) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (leaf : P e.callee = none)
    (meaning : PV_THR2_SourceStoreNative.function e.callee = some f) :
    PV_LIB_A_SourceWriters.law C values (pending e) w es e.suspended
      (PV_LIB_A_WriterSites.site e f) (H (PV_LIB_A_WriterSites.site e f).waiting.request w)
      (PV_LIB.observe (PV_LIB_A_OwnerStore.step C K P resources encode H values
        ⟨⟨.running (pending e),w,es⟩,e.suspended⟩)) :=
  PV_LIB_A_WriterSites.installed C K P resources encode H values e f w es leaf meaning
    (noncatch e f meaning)
#print axioms noncatch
#print axioms installed
end PV_LIB_A_WriterOrdinary
