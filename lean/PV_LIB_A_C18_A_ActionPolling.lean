import PV_LIB_A_CellSetPatch
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActionPolling
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
abbrev BaseState := PV_LIB_StoreActionTable.State
abbrev Site := PV_LIB_StoreActionTable.Site
abbrev Handler := PV_LIB_StoreActionTable.Handler

/-- A pending action has already executed its source-store prefix. The retained
site is control state, not a new source/OWNER allocation or an endpoint premise. -/
structure State where
  base : BaseState
  applied : Option Site := none

def projection (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (site : Site) (s : Store Data) (w : OWNER)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : Option (Store Data) :=
  match site.action with
  | .cellBoolSet504 => match PV_LIB_A_CellSetBegin.destructor site.callee with
    | some d => if PV_LIB_A_CellSetBegin.trivial d then
        PV_LIB_A_CellSetBegin.PV_THR2_LibrarySemantics_CellSetTrivial504 C site.callee site.arguments s w
      else PV_LIB_StoreActionTable.interpret C values site.action site.callee site.arguments s w r
    | none => PV_LIB_StoreActionTable.interpret C values site.action site.callee site.arguments s w r
  | _ => PV_LIB_StoreActionTable.interpret C values site.action site.callee site.arguments s w r

/-- Delivery never re-executes the source action. Pending keeps the SAME saved
native request; other replies use the pinned status/store/world/event rule. -/
def receive (C : Carrier OWNER Data) (c : Config) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (site : Site) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : State :=
  let q := PV_THR2_ChildBoundary.delivered C c site.waiting r
  ⟨⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩,
    match r.answer with | .pending => some site | _ => none⟩

/-- Initial prefix application. Coverage is STILL partial: typed nontrivial
Drop and the inherited missing wrappers cannot be certified by this mechanism. -/
def begin (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : Site) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : State :=
  match projection C values site c.store w r with
  | none => ⟨⟨⟨.undefined none c.store,r.world,es ++ r.events⟩,stack⟩,none⟩
  | some post => receive C {c with store := post} es stack site r

/-- The original resource channel and OWNER-aware base are reused unchanged.
When the phase is retained, the next poll cannot re-enter `projection`. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) : State :=
  match s.applied with
  | some site => match s.base.current.status with
    | .running c => receive C c s.base.current.events s.base.suspended site
        (H site.waiting.request s.base.current.world)
    | _ => ⟨s.base,none⟩
  | none => match s.base.current.status with
    | .running c => match PV_THR2_Catch316Segment.select c with
      | some _ => ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s.base,none⟩
      | none => match PV_LIB_StoreActionTable.select P c with
        | none => ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s.base,none⟩
        | some site => begin C values c s.base.current.world s.base.current.events s.base.suspended site
            (H site.waiting.request s.base.current.world)
    | _ => ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s.base,none⟩

/-- Exact full-reply graph on retries, independent of values/projection.
No success, nonlast, no-write or overflow-free restriction appears. -/
theorem retry (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (c : Config)
    (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : Site) :
    step C K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,some site⟩ =
      receive C c es stack site (H site.waiting.request w) := rfl

theorem pending (C : Carrier OWNER Data) (c : Config)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : Site) (post : OWNER) :
    receive C c es stack site ⟨.pending,post,events⟩ =
      ⟨⟨⟨.running c,post,es ++ events⟩,stack⟩,some site⟩ := rfl

/-- Every repeated pending answer retains the already-written source store,
original waiting request, saved frames, and exact new world/event suffix. -/
theorem pending_retry (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (c : Config)
    (w post : OWNER) (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : Site)
    (answer : H site.waiting.request w = ⟨.pending,post,events⟩) :
    step C K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,some site⟩ =
      ⟨⟨⟨.running c,post,es ++ events⟩,stack⟩,some site⟩ := by
  rw [retry,answer]
  rfl

/-- One symbolic agreement with the OWNER base outside selected actions. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : BaseState)
    (away : PV_LIB_StoreActionTable.Neutral P s) :
    step C K P resources encode H values ⟨s,none⟩ =
      ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s,none⟩ := by
  unfold step
  cases hs : s.current.status <;> try rfl
  rename_i c
  cases hc : PV_THR2_Catch316Segment.select c <;> simp only [hc,away c hs]

#print axioms projection
#print axioms receive
#print axioms begin
#print axioms step
#print axioms retry
#print axioms pending
#print axioms pending_retry
#print axioms agreement
end PV_LIB_A_ActionPolling
