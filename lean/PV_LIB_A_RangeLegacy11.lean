import PV_LIB_A_RangeRetry11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeLegacy11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

def oldSite (s : Store Data) (a : Nat) : PV_LIB_StoreActionTable.Site :=
  ⟨.legacy .rangeNext93,PV_THR2_Source15RangeChild.fn93,
    (PV_LIB_A_RangePoll11.site s a).waiting,(PV_LIB_A_RangePoll11.site s a).arguments⟩

theorem selected (P : Data → Option PV_STX2_SliceSyntax.Program)
    (s : Store Data) (a : Nat) (parents : List Frame) :
    select (PV_LIB_A_RangePoll11.programs P) (PV_THR2_Source15Loop93Issue.pending s a parents) =
      some (oldSite s a) := by
  unfold select
  change (match PV_LIB_A_RangePoll11.programs P PV_THR2_Source15RangeChild.fn93 with
    | some _ => none
    | none => (v2 PV_THR2_Source15RangeChild.fn93).bind _) = _
  rw [show PV_LIB_A_RangePoll11.programs P PV_THR2_Source15RangeChild.fn93 = none from
    PV_THR2_Source15RangeChild.child93 P]
  rfl

/-- Initial source-phase delivery projects to the exact legacy v2 delivery on
EVERY answer. Undefined input stays undefined on both sides; this equality is
not a whole-table adequacy claim. -/
theorem begin_projects (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (s : Store Data) (a : Nat) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    (sourceBegin C values c w es stack (PV_LIB_A_RangePoll11.site s a) r).base =
      deliver C values c w es stack (oldSite s a) r := by
  unfold sourceBegin
  change (match (PV_THR2_LibrarySemantics_RangeNext93 C
      (PV_LIB_A_RangePoll11.site s a).arguments c.store w).map
      (fun post => (⟨post,.done⟩ : Started)) with
    | none => _
    | some begun => sourceReceive C {c with store := begun.store} es stack
        (PV_LIB_A_RangePoll11.site s a) begun.tail r).base = _
  unfold deliver
  change _ = (match PV_THR2_LibrarySemantics_RangeNext93 C
      (PV_LIB_A_RangePoll11.site s a).arguments c.store w with
    | none => _
    | some post => _)
  cases result : PV_THR2_LibrarySemantics_RangeNext93 C
      (PV_LIB_A_RangePoll11.site s a).arguments c.store w with
  | none => rfl
  | some post => exact source_done_reply C {c with store := post} es stack _ r

/-- Lane C can reuse its initial legacy v2 poll proof via this projection.
Pending retries must keep the new source phase (RangeRetry11); repeatedly
invoking the legacy step has no such guarantee. -/
theorem initial_poll (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let c := PV_THR2_Source15Loop93Issue.pending s a parents
    let q : State := ⟨⟨.running c,w,es⟩,stack⟩
    (PV_LIB_A_DeferredActions.step C K (PV_LIB_A_RangePoll11.programs P) resources encode H values ⟨q,none⟩).base =
      PV_LIB_StoreActionTable.step C K (PV_LIB_A_RangePoll11.programs P) resources encode H values q := by
  intro c q
  have ordinary : PV_THR2_Catch316Segment.select c = none := rfl
  change (sourceStep C K (PV_LIB_A_RangePoll11.programs P) resources encode H values ⟨q,none⟩).base = _
  rw [source_native C K _ resources encode H values c w es stack _ ordinary
      (PV_LIB_A_RangePoll11.selected P s a parents),
    PV_LIB_StoreActionTable.native C K _ resources encode H values c w es stack _ ordinary (selected P s a parents)]
  exact begin_projects C values c w es stack s a _

#print axioms selected
#print axioms begin_projects
#print axioms initial_poll
end PV_LIB_A_RangeLegacy11
