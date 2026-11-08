import PV_LIB_A_FetchSubMachine10
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_FetchSubRetry10
open scoped Classical
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_FetchSubReply10 PV_LIB_A_FetchSubMachine10

/-- Exact retry graph: sourceReceive consumes the native reply without running
sourceStart or another subtraction. The saved pre-subtraction value is used on
ALL returned answers, even after arbitrarily many pending source phases. -/
theorem graph (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (old : Nat)
    (action : site.action = .inherited (.primitive .fetchSub581))
    (waiting : c.frame.waiting = some site.waiting) :
    step C K P resources encode H values
      ⟨⟨⟨⟨.running c,w,es⟩,stack⟩,some (site,.done)⟩,some ⟨site.waiting,old⟩⟩ =
      let out := sourceReceive
        (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K)
        c es stack site .done
        (PV_THR2_LibrarySemantics_FetchSubValue581 old (H site.waiting.request w))
      ⟨out,if out.applied.isSome then some ⟨site.waiting,old⟩ else none⟩ := by
  simp [PV_LIB_A_FetchSubMachine10.step,poll,action,waiting,PV_LIB_A_WeakOwnerFree10.step,
    PV_LIB_A_WeakOwnerFree9.step,v2ProvenanceStep,PV_LIB_A_GenericDropMachine9.step,
    PV_LIB_A_DeferredActions.step,PV_LIB_A_DeferredActions.deferred,sourceStep,PV_LIB_A_FetchSubReply10.handler]

/-- Repeated pending answers preserve the already-decremented source config,
original wait, count snapshot, lower frames, and exact new world/event suffix. -/
theorem pending (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w post : OWNER) (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (old : Nat)
    (action : site.action = .inherited (.primitive .fetchSub581))
    (waiting : c.frame.waiting = some site.waiting)
    (answer : H site.waiting.request w = ⟨.pending,post,events⟩) :
    step C K P resources encode H values
      ⟨⟨⟨⟨.running c,w,es⟩,stack⟩,some (site,.done)⟩,some ⟨site.waiting,old⟩⟩ =
      ⟨⟨⟨⟨.running c,post,es ++ events⟩,stack⟩,some (site,.done)⟩,
        some ⟨site.waiting,old⟩⟩ := by
  rw [graph C K P resources encode H values c w es stack site old action waiting,answer]
  simp only [PV_LIB_A_FetchSubReply10.pending,source_pending,Option.isSome_some,if_true]

/-- Initial capture reads the old source value before invoking the existing
write/delivery machinery. Read failure remains the machine's explicit gap. -/
theorem begin (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (old : Nat)
    (selection : selected P c = some site)
    (source : readOld (PV_LIB_A_UnwindMatch.carrier (PV_THR2_AggregateCompletion.carrier C) K)
      c w site = some old) :
    step C K P resources encode H values (wrap ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩) =
      poll C K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ ⟨site.waiting,old⟩ := by
  simp only [PV_LIB_A_FetchSubMachine10.step,wrap,selection,source]

#print axioms graph
#print axioms pending
#print axioms begin
end PV_LIB_A_FetchSubRetry10
