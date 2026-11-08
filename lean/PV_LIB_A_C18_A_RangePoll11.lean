import PV_LIB_A_RangeTraceV2
import PV_LIB_A_DeferredActions
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangePoll11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

def programs (P : Data → Option PV_STX2_SliceSyntax.Program) :=
  PV_THR2_Source208Table.table (PV_THR2_Source15Table.resolve (PV_THR2_OwnInitChildren.resolve P))

def site (s : Store Data) (a : Nat) : SourceSite :=
  ⟨.inherited (.legacy .rangeNext93),PV_THR2_Source15RangeChild.fn93,
    PV_THR2_StaticReply.wait (PV_THR2_Source15Loop93Issue.prepared s a)
      PV_THR2_Source15RangeChild.fn93 [PV_THR2_Source15Loop93Issue.ref a] 8,
    [PV_THR2_Source15Loop93Issue.ref a]⟩

/-- Exact emitted3447 request, including its actual saved activation/destination.
The resolver fact is the provider's opaque93 theorem, not a caller premise. -/
theorem selected (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) :
    sourceSelect (programs P) (PV_THR2_Source15Loop93Issue.pending s a parents) =
      some (site s a) := by
  unfold sourceSelect
  change (match programs P PV_THR2_Source15RangeChild.fn93 with
    | some _ => none
    | none => (v2Source PV_THR2_Source15RangeChild.fn93).bind
        (fun action => some (⟨action,PV_THR2_Source15RangeChild.fn93,
          (site s a).waiting,(site s a).arguments⟩ : SourceSite))) = _
  rw [show programs P PV_THR2_Source15RangeChild.fn93 = none from
    PV_THR2_Source15RangeChild.child93 P]
  rfl

/-- Bind the corrected poll to the SAME source-created iterator. Every reply
is retained; no success/write-definedness premise is introduced for93. -/
theorem poll (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (b : Bool)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (start finish : Nat)
    (cell : (PV_THR2_Source15Loop93Issue.pending s a parents).store.cells ⟨a,7,[]⟩ =
      some (PV_LIB_A_Range165.sourceRange start finish)) :
    let B := PV_THR2_OwnInitExactReturnedCases.carrier C b
    let c := PV_THR2_Source15Loop93Issue.pending s a parents
    let post := if start < finish then
      write c.store ⟨a,7,[]⟩ (some (PV_LIB_A_Range165.sourceRange (start+1) finish)) else c.store
    PV_LIB_A_DeferredActions.step B K (programs P) resources encode H values
      ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ =
      sourceReceive B {c with store := post} es stack (site s a) .done
        (H (site s a).waiting.request w) := by
  intro B c post
  have ordinary : PV_THR2_Catch316Segment.select c = none := rfl
  unfold PV_LIB_A_DeferredActions.step
  change sourceStep B K (programs P) resources encode H values _ = _
  rw [source_native B K (programs P) resources encode H values c w es stack
    (site s a) ordinary (selected P s a parents)]
  have meaning : PV_LIB_StoreActionTable.start B values (site s a).action
      (site s a).callee (site s a).arguments c.store w
      (H (site s a).waiting.request w) = some ⟨post,.done⟩ := by
    change (PV_THR2_LibrarySemantics_RangeNext93 B
      [PV_THR2_Source15Loop93Issue.ref a] c.store w).map
      (fun t => (⟨t,.done⟩ : Started)) = _
    have writeLaw := PV_LIB_A_RangeWriter.range93 C b c.store w a start finish .null cell
    change PV_THR2_LibrarySemantics_RangeNext93 B
      [PV_THR2_Source15Loop93Issue.ref a] c.store w = some post at writeLaw
    rw [writeLaw]
    rfl
  unfold sourceBegin
  rw [meaning]

#print axioms selected
#print axioms poll
end PV_LIB_A_RangePoll11
