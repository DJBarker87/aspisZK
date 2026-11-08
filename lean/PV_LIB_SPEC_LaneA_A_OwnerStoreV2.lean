import PV_LIB_A_ScopeDispatchV2
import PV_LIB_A_CellTakeV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_OwnerStoreV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_THR2_SourceStoreLibrary
abbrev State := PV_LIB_A_OwnerStore.State
abbrev Handler := PV_LIB_A_OwnerStore.Handler
abbrev Site := PV_STX2_Native.Waiting Data × List Data

def select (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config) : Option Site := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request with
    | .child fn _ args =>
      match P fn with
      | some _ => none
      | none => if PV_THR2_OffPath.functionId fn = some 641 then some (wait,args) else none
    | _ => none

/-- D984 correction CANDIDATE: original five plus fourteen additional named
source projections, on the unchanged OWNER-aware bridged base. Typed Drop and
last-strong destructor composition are still open. This is never credited as
full source/machine adequacy or consumed in a row proof. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) : State :=
  match s.current.status with
  | .running c => match PV_THR2_Catch316Segment.select c with
    | some _ => PV_LIB_A_ScopeDispatchV2.step C K P resources encode H values s
    | none => match select P c with
      | none => PV_LIB_A_ScopeDispatchV2.step C K P resources encode H values s
      | some site =>
        let r := H site.1.request s.current.world
        match PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_CellTake641 C site.2 c.store s.current.world with
        | none => ⟨⟨.undefined none c.store,r.world,s.current.events ++ r.events⟩,s.suspended⟩
        | some store =>
          let q := PV_THR2_ChildBoundary.delivered C {c with store := store} site.1 r
          ⟨⟨q.status,q.world,s.current.events ++ q.events⟩,s.suspended⟩
  | _ => PV_LIB_A_ScopeDispatchV2.step C K P resources encode H values s

def Neutral (P : Data → Option PV_STX2_SliceSyntax.Program) (s : State) : Prop :=
  ∀ c, s.current.status = .running c →
    select P c = none ∧ PV_LIB_A_ScopeDispatchV2.select P c = none ∧
      PV_LIB_A_StoreDispatchV2.select P c = none ∧ PV_THR2_SourceStoreNative.select P c = none

theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (away : Neutral P s) :
    step C K P resources encode H values s =
      PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s := by
  have same : step C K P resources encode H values s =
      PV_LIB_A_ScopeDispatchV2.step C K P resources encode H values s := by
    unfold step
    cases hs : s.current.status <;> try rfl
    rename_i c
    cases hc : PV_THR2_Catch316Segment.select c <;> simp only [hc,(away c hs).1]
  exact same.trans (PV_LIB_A_ScopeDispatchV2.agreement C K P resources encode H values s
    (fun c hs => (away c hs).2.1) (fun c hs => (away c hs).2.2.1) (fun c hs => (away c hs).2.2.2))

def advance (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) : Nat → State → State
  | 0,s => s
  | n+1,s => advance C K P resources encode H values n (step C K P resources encode H values s)

/-- Trace-indexed, on the same already-proved OWNER run. No global bisimulation
or site-by-site source re-execution is required. -/
def NeutralTrace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) : Nat → State → Prop
  | 0,_ => True
  | n+1,s => Neutral P s ∧ NeutralTrace C K P resources encode H n
      (PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s)

theorem advance_agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (n : Nat) (s : State)
    (trace : NeutralTrace C K P resources encode H n s) :
    advance C K P resources encode H values n s =
      PV_THR2_OwnInitInterpreterBridged.advance C K P resources encode H n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change advance C K P resources encode H values n
      (step C K P resources encode H values s) = _
    rw [agreement C K P resources encode H values s trace.1]
    exact ih _ trace.2

theorem effects (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : Site) (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select P c = some site) :
    let r := H site.1.request w
    let out := step C K P resources encode H values ⟨⟨.running c,w,es⟩,stack⟩
    out.current.world = r.world ∧ out.current.events = es ++ r.events ∧ out.suspended = stack := by
  simp only [step,ordinary,selected]
  cases meaning : PV_LIB_A_CellTakeV2.PV_THR2_LibrarySemantics_CellTake641 C site.2 c.store w with
  | none => exact ⟨rfl,rfl,rfl⟩
  | some store =>
    have h := PV_THR2_ChildBoundary.effects C {c with store := store} site.1 (H site.1.request w)
    exact ⟨h.1,congrArg (es ++ ·) h.2,rfl⟩

#print axioms agreement
#print axioms advance_agreement
#print axioms effects
end PV_LIB_A_OwnerStoreV2
