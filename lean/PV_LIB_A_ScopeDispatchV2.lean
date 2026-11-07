import PV_LIB_A_StoreDispatchV2
import PV_LIB_A_ScopeStoreV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ScopeDispatchV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_THR2_SourceStoreLibrary
abbrev State := PV_LIB_A_StoreDispatchV2.State
abbrev Handler := PV_LIB_A_StoreDispatchV2.Handler

inductive Function where
  | increment457 | decrement611
  deriving DecidableEq

def function : Data → Option Function
  | .object [("Regular",.object [("kind",.object [("Fun",.object
      [("Regular",.number n)])]),("generics",_)])] =>
    match n with
    | 457 => some .increment457
    | 611 => some .decrement611
    | _ => none
  | _ => none

structure Site where
  meaning : Function
  callee : Data
  waiting : PV_STX2_Native.Waiting Data
  arguments : List Data

def select (P : Data → Option PV_STX2_SliceSyntax.Program) (c : Config) : Option Site := do
  match c.frame.completed with
  | some _ => none
  | none =>
    let wait ← c.frame.waiting
    match wait.request with
    | .child fn _ args =>
      match P fn with
      | some _ => none
      | none =>
        let f ← function fn
        pure ⟨f,fn,wait,args⟩
    | _ => none

def interpret (C : Carrier OWNER Data) (f : Function) (args : List Data)
    (s : Store Data) (w : OWNER) : Option (Store Data) :=
  match f with
  | .increment457 => PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeIncrement457 C args s w
  | .decrement611 => PV_LIB_A_ScopeStoreV2.PV_THR2_LibrarySemantics_ScopeDecrement611 C args s w

/-- Count-projection extension candidate only. Full source/runtime adequacy,
including the unpark codec/footprint, remains open; no row consumes this. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) : State :=
  match s.current.status with
  | .running c => match PV_THR2_Catch316Segment.select c with
    | some _ => PV_LIB_A_StoreDispatchV2.step C K P resources encode H values s
    | none => match select P c with
      | none => PV_LIB_A_StoreDispatchV2.step C K P resources encode H values s
      | some site =>
        let r := H site.waiting.request s.current.world
        match interpret C site.meaning site.arguments c.store s.current.world with
        | none => ⟨⟨.undefined none c.store,r.world,s.current.events ++ r.events⟩,s.suspended⟩
        | some store =>
          let q := PV_THR2_ChildBoundary.delivered C {c with store := store} site.waiting r
          ⟨⟨q.status,q.world,s.current.events ++ q.events⟩,s.suspended⟩
  | _ => PV_LIB_A_StoreDispatchV2.step C K P resources encode H values s

/-- Agreement at neutral configurations is with the OWNER-aware machine.
All three selectors must be neutral; no registration layer is dropped. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (scopeAway : ∀ c, s.current.status = .running c → select P c = none)
    (newAway : ∀ c, s.current.status = .running c → PV_LIB_A_StoreDispatchV2.select P c = none)
    (oldAway : ∀ c, s.current.status = .running c → PV_THR2_SourceStoreNative.select P c = none) :
    step C K P resources encode H values s =
      PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s := by
  have same : step C K P resources encode H values s =
      PV_LIB_A_StoreDispatchV2.step C K P resources encode H values s := by
    unfold step
    cases hs : s.current.status <;> try rfl
    rename_i c
    cases hc : PV_THR2_Catch316Segment.select c <;> simp only [hc,scopeAway c hs]
  exact same.trans (PV_LIB_A_StoreDispatchV2.agreement_owner C K P resources encode H values s newAway oldAway)

theorem effects (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : Site) (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select P c = some site) :
    let r := H site.waiting.request w
    let out := step C K P resources encode H values ⟨⟨.running c,w,es⟩,stack⟩
    out.current.world = r.world ∧ out.current.events = es ++ r.events ∧ out.suspended = stack := by
  simp only [step,ordinary,selected]
  cases meaning : interpret C site.meaning site.arguments c.store w with
  | none => exact ⟨rfl,rfl,rfl⟩
  | some store =>
    have h := PV_THR2_ChildBoundary.effects C {c with store := store} site.waiting
      (H site.waiting.request w)
    exact ⟨h.1,congrArg (es ++ ·) h.2,rfl⟩

#print axioms interpret
#print axioms agreement
#print axioms effects
end PV_LIB_A_ScopeDispatchV2
