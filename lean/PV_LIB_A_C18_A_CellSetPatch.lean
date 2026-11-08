import PV_LIB_A_C18_A_CellSetBegin
import PV_LIB_SPEC_LaneA_A_StoreActionMachine
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_CellSetPatch
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_A_CellSetBegin
abbrev State := PV_LIB_StoreActionTable.State
abbrev Handler := PV_LIB_StoreActionTable.Handler
abbrev Site := PV_LIB_StoreActionTable.Site

/-- An overlay for the exact trivial504 specializations. Nontrivial destructors
remain in the inherited table and are NOT silently treated as trivial. -/
def select (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config) : Option Site := do
  let site ← PV_LIB_StoreActionTable.select P c
  match site.action with
  | .cellBoolSet504 =>
    let d ← destructor site.callee
    if trivial d then some site else none
  | _ => none

def deliver (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : Site)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : State :=
  match PV_THR2_LibrarySemantics_CellSetTrivial504 C site.callee site.arguments c.store w with
  | none => ⟨⟨.undefined none c.store,r.world,es ++ r.events⟩,stack⟩
  | some store =>
    let q := PV_THR2_ChildBoundary.delivered C {c with store := store} site.waiting r
    ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩

def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) : State :=
  match s.current.status with
  | .running c => match PV_THR2_Catch316Segment.select c with
    | some _ => PV_LIB_StoreActionTable.step C K P resources encode H values s
    | none => match select P c with
      | none => PV_LIB_StoreActionTable.step C K P resources encode H values s
      | some site => deliver C c s.current.world s.current.events s.suspended site
          (H site.waiting.request s.current.world)
  | _ => PV_LIB_StoreActionTable.step C K P resources encode H values s

/-- The single unchanged OWNER base, including its resource environment. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (away : PV_LIB_StoreActionTable.Neutral P s) :
    step C K P resources encode H values s =
      PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s := by
  have same : step C K P resources encode H values s =
      PV_LIB_StoreActionTable.step C K P resources encode H values s := by
    unfold step
    cases hs : s.current.status <;> try rfl
    rename_i c
    have noSite : select P c = none := by
      unfold select
      rw [away c hs]
      rfl
    cases hc : PV_THR2_Catch316Segment.select c <;> simp only [hc,noSite]
  exact same.trans (PV_LIB_StoreActionTable.agreement C K P resources encode H values s away)

/-- ALL replies use exactly the pinned child-delivery rule after replacement.
The premises describe source reads/writes and metadata, never success of r. -/
theorem full_reply (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (site : Site)
    (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) (post : Store Data)
    (old reference value : Data) (d : Destructor) (p : Address)
    (args : site.arguments = [reference,value])
    (metadata : destructor site.callee = some d)
    (received : receiver C c.store w reference = some (p,old))
    (replaced : writeAddress C c.store p (some value) = some post)
    (typed : trivial d = true) :
    deliver C c w es stack site r =
      let q := PV_THR2_ChildBoundary.delivered C {c with store := post} site.waiting r
      ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩ := by
  have start := begin_from_source C c.store post w site.callee reference value old d p
    metadata received replaced
  unfold deliver PV_THR2_LibrarySemantics_CellSetTrivial504
  rw [args,start]
  change (match (if trivial d = true then some post else none) with
    | none => _
    | some store => _) = _
  rw [typed]
  rfl

#print axioms select
#print axioms deliver
#print axioms step
#print axioms agreement
#print axioms full_reply
end PV_LIB_A_CellSetPatch
