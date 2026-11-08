import PV_LIB_A_RangeFirst11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_RangeRetry11
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable

/-- A pending93 has already incremented the iterator. Keep its SAME wait token
and exact written store; no new poll executes the initial operation again. -/
theorem pending (C : Carrier OWNER Data) (s : Store Data) (a : Nat)
    (parents : List Frame) (value : Data) (es events : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (w : OWNER) :
    sourceReceive C (PV_LIB_A_RangeFirst11.afterWrite s a parents value) es stack
      (PV_LIB_A_RangePoll11.site (PV_LIB_A_RangeHistoryV2.iteratorStore s a value) a) .done
      ⟨.pending,w,events⟩ =
      ⟨⟨⟨.running (PV_LIB_A_RangeFirst11.afterWrite s a parents value),w,es ++ events⟩,stack⟩,
        some (PV_LIB_A_RangePoll11.site (PV_LIB_A_RangeHistoryV2.iteratorStore s a value) a,.done)⟩ :=
  source_pending C _ es events stack _ .done w

/-- Exact all-answer retry at the actual3447 request. Source iterator, lower
frames and suspended frames are unchanged by the retry operation itself. -/
theorem retry (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (value : Data)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    let c := PV_LIB_A_RangeFirst11.afterWrite s a parents value
    let site := PV_LIB_A_RangePoll11.site (PV_LIB_A_RangeHistoryV2.iteratorStore s a value) a
    PV_LIB_A_DeferredActions.step C K P resources encode H values
      ⟨⟨⟨.running c,w,es⟩,stack⟩,some (site,.done)⟩ =
      sourceReceive C c es stack site .done (H site.waiting.request w) := by
  intro c site
  rfl

/-- A repeated pending answer preserves the actual source iterator at2, rather
than manufacturing3; all world/event effects still come from the full reply. -/
theorem pending_retry (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (s : Store Data) (a : Nat) (parents : List Frame) (value : Data)
    (w post : OWNER) (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (answer : H (PV_LIB_A_RangePoll11.site (PV_LIB_A_RangeHistoryV2.iteratorStore s a value) a).waiting.request w =
      ⟨.pending,post,events⟩) :
    let c := PV_LIB_A_RangeFirst11.afterWrite s a parents value
    let site := PV_LIB_A_RangePoll11.site (PV_LIB_A_RangeHistoryV2.iteratorStore s a value) a
    PV_LIB_A_DeferredActions.step C K P resources encode H values
      ⟨⟨⟨.running c,w,es⟩,stack⟩,some (site,.done)⟩ =
      ⟨⟨⟨.running c,post,es ++ events⟩,stack⟩,some (site,.done)⟩ := by
  intro c site
  rw [retry,answer]
  exact pending C s a parents value es events stack post

#print axioms pending
#print axioms retry
#print axioms pending_retry
end PV_LIB_A_RangeRetry11
