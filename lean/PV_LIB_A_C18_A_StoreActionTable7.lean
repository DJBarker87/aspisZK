import PV_LIB_A_C18_A_ActionPolling
import PV_LIB_A_C18_A_CellSetThreadId
import PV_LIB_A_C18_A_WeakDropSource
import PV_LIB_A_C18_A_ThreadCloneStore
set_option autoImplicit false
noncomputable section
namespace PV_LIB_StoreActionTable
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary

/-- Session7 extension. The old v2 and its checked counterexamples are retained
unchanged/importable. This is still PARTIAL: no arbitrary-T/last-strong/wrapper
adequacy is inferred from its name or from a deterministic graph identity. -/
inductive SourceAction where
  | inherited (action : Action)
  | cellSet504 | weakDrop683 | threadClone214

def v2Source (fn : Data) : Option SourceAction :=
  match PV_THR2_OffPath.functionId fn with
  | some 504 => some .cellSet504
  | some 683 => some .weakDrop683
  | some 214 => some .threadClone214
  | _ => (v2 fn).map SourceAction.inherited

/-- Complete Cell copy-type projections, staged source-backed Weak drops, and
the source-backed Thread clone are distinguished from inherited projections.
Native value/world/order/backing instances remain lower obligations. -/
inductive SourceCoverage where
  | inherited (coverage : Coverage)
  | copyTypesOnly | sourceBackedWeak | sourceBackedThread

def sourceCoverage : SourceAction → SourceCoverage
  | .inherited action => .inherited (coverage action)
  | .cellSet504 => .copyTypesOnly
  | .weakDrop683 => .sourceBackedWeak
  | .threadClone214 => .sourceBackedThread

abbrev Tail := PV_LIB_A_WeakDropSource.Tail
abbrev Started := PV_LIB_A_WeakDropSource.Started

def start (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (action : SourceAction) (fn : Data) (args : List Data) (s : Store Data) (w : OWNER)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : Option Started :=
  match action with
  | .inherited action => (interpret C values action fn args s w r).map (fun post => ⟨post,.done⟩)
  | .cellSet504 =>
    (PV_LIB_A_CellSetThreadId.PV_THR2_LibrarySemantics_CellSetCopy504 C fn args s w).map
      (fun post => ⟨post,.done⟩)
  | .weakDrop683 => PV_LIB_A_WeakDropSource.PV_THR2_LibrarySemantics_WeakDropBegin683 C args s w
  | .threadClone214 =>
    (PV_LIB_A_ThreadCloneStore.PV_THR2_LibrarySemantics_ThreadCloneSource214 C args s w).map
      (fun post => ⟨post,.done⟩)

structure SourceSite where
  action : SourceAction
  callee : Data
  waiting : PV_STX2_Native.Waiting Data
  arguments : List Data

def sourceSelect (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config) : Option SourceSite := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request with
    | .child fn _ args =>
      match P fn with
      | some _ => none
      | none =>
        let action ← v2Source fn
        pure ⟨action,fn,wait,args⟩
    | _ => none

/-- The phase contains fixed source control data, never a supplied Store map.
It names the same already-applied native prefix and optional deallocation. -/
structure SourceState where
  base : State
  applied : Option (SourceSite × Tail) := none

def sourceReceive (C : Carrier OWNER Data) (c : Config)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (tail : Tail) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : SourceState :=
  match PV_LIB_A_WeakDropSource.finish C tail c.store r with
  | none => ⟨⟨⟨.undefined none c.store,r.world,es ++ r.events⟩,stack⟩,none⟩
  | some post =>
    let q := PV_THR2_ChildBoundary.delivered C {c with store := post} site.waiting r
    ⟨⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩,
      match r.answer with | .pending => some (site,tail) | _ => none⟩

def sourceBegin (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : SourceState :=
  match start C values site.action site.callee site.arguments c.store w r with
  | none => ⟨⟨⟨.undefined none c.store,r.world,es ++ r.events⟩,stack⟩,none⟩
  | some begun => sourceReceive C {c with store := begun.store} es stack site begun.tail r

/-- The OWNER-aware base is unchanged. A retained source phase polls the SAME
request and never re-executes the initial Cell/count/iterator write. -/
def sourceStep (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : SourceState) : SourceState :=
  match s.applied with
  | some (site,tail) => match s.base.current.status with
    | .running c => sourceReceive C c s.base.current.events s.base.suspended site tail
        (H site.waiting.request s.base.current.world)
    | _ => ⟨s.base,none⟩
  | none => match s.base.current.status with
    | .running c => match PV_THR2_Catch316Segment.select c with
      | some _ => ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s.base,none⟩
      | none => match sourceSelect P c with
        | none => ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s.base,none⟩
        | some site => sourceBegin C values c s.base.current.world s.base.current.events
            s.base.suspended site (H site.waiting.request s.base.current.world)
    | _ => ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s.base,none⟩

def SourceNeutral (P : Data → Option PV_STX2_SliceSyntax.Program) (s : State) : Prop :=
  ∀ c, s.current.status = .running c → sourceSelect P c = none

/-- ONE symbolic agreement against the identical OWNER interpreter and resource
channel, away from ALL old/new selected actions and before a retained phase. -/
theorem source_agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (away : SourceNeutral P s) :
    sourceStep C K P resources encode H values ⟨s,none⟩ =
      ⟨PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s,none⟩ := by
  unfold sourceStep
  cases hs : s.current.status <;> try rfl
  rename_i c
  cases hc : PV_THR2_Catch316Segment.select c <;> simp only [hc,away c hs]

/-- The exact source-only graph at the selected poll; ALL native answers are
inputs. Unsupported branches remain exposed and earn no source adequacy. -/
theorem source_native (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : sourceSelect P c = some site) :
    sourceStep C K P resources encode H values ⟨⟨⟨.running c,w,es⟩,stack⟩,none⟩ =
      sourceBegin C values c w es stack site (H site.waiting.request w) := by
  simp only [sourceStep,ordinary,selected]

/-- No repeated source writes on pending retries, even for a last Weak whose
source block has not yet been deallocated. -/
theorem source_pending (C : Carrier OWNER Data) (c : Config)
    (es events : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : SourceSite) (tail : Tail) (w : OWNER) :
    sourceReceive C c es stack site tail ⟨.pending,w,events⟩ =
      ⟨⟨⟨.running c,w,es ++ events⟩,stack⟩,some (site,tail)⟩ := by
  unfold sourceReceive
  rw [PV_LIB_A_WeakDropSource.pending]
  rfl

theorem source_done_reply (C : Carrier OWNER Data) (c : Config)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : SourceSite)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    (sourceReceive C c es stack site .done r).base =
      let q := PV_THR2_ChildBoundary.delivered C c site.waiting r
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  cases r.answer <;> rfl

#print axioms v2Source
#print axioms sourceCoverage
#print axioms start
#print axioms sourceSelect
#print axioms sourceReceive
#print axioms sourceBegin
#print axioms sourceStep
#print axioms source_agreement
#print axioms source_native
#print axioms source_pending
#print axioms source_done_reply
end PV_LIB_StoreActionTable
