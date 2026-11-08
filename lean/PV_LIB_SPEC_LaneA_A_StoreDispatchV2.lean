import PV_LIB_SPEC_LaneA_A_ArcStoreV2
import PV_LIB_SPEC_LaneA_A_StoreAtomicV2
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_StoreDispatchV2
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_THR2_SourceStoreLibrary
open PV_LIB_A_StorePrimitiveV2
/-- Implemented extra native source writers only. This is NOT a claim of full
D984 coverage: typed Drop, whole native wrappers and Cell::take remain open.
Original five meanings are inherited without editing their proved modules. -/
inductive Function where
  | arcClone360 | fetchAdd351 | fetchSub581 | store557 | boolStore646
  | memReplace442 | ptrWrite308 | ptrWrite364 | cellSet504 | cas530 | cas555
  deriving DecidableEq

def function : Data → Option Function
  | .object [("Regular",.object [("kind",.object [("Fun",.object
      [("Regular",.number n)])]),("generics",_)])] =>
    match n with
    | 360 => some .arcClone360
    | 351 => some .fetchAdd351
    | 581 => some .fetchSub581
    | 557 => some .store557
    | 646 => some .boolStore646
    | 442 => some .memReplace442
    | 308 => some .ptrWrite308
    | 364 => some .ptrWrite364
    | 504 => some .cellSet504
    | 530 => some .cas530
    | 555 => some .cas555
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

/-- Each branch names exactly one documented source meaning. No supplied
Store transformer, success premise or identity delta is accepted. -/
def interpret {W E : Type} (C : Carrier W Data) (f : Function)
    (args : List Data) (s : Store Data) (w : W) (r : Reply W E Data) : Option (Store Data) :=
  match f with
  | .arcClone360 => PV_LIB_A_ArcStoreV2.PV_THR2_LibrarySemantics_ArcClone360 C args s w
  | .fetchAdd351 => PV_THR2_LibrarySemantics_FetchAdd351 C args s w
  | .fetchSub581 => PV_THR2_LibrarySemantics_FetchSub581 C args s w
  | .store557 => PV_THR2_LibrarySemantics_AtomicStore557 C args s w
  | .boolStore646 => PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_AtomicBoolStore646 C args s w
  | .memReplace442 => PV_THR2_LibrarySemantics_MemReplace442 C args s w
  | .ptrWrite308 => PV_THR2_LibrarySemantics_PtrWrite308 C args s w
  | .ptrWrite364 => PV_THR2_LibrarySemantics_PtrWrite364 C args s w
  | .cellSet504 => PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CellSet504 C args s w
  | .cas530 => PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchangeWeak530 C args s w r
  | .cas555 => PV_LIB_A_StoreAtomicV2.PV_THR2_LibrarySemantics_CompareExchange555 C args s w r

abbrev State := PV_LIB_A_OwnerStore.State
abbrev Handler := PV_LIB_A_OwnerStore.Handler

def deliver (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : Site) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : State :=
  match interpret C site.meaning site.arguments c.store w r with
  | none => ⟨⟨.undefined none c.store,r.world,es ++ r.events⟩,stack⟩
  | some store =>
    let q := PV_THR2_ChildBoundary.delivered C {c with store := store} site.waiting r
    ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩

/-- Extension candidate with exact implemented primitive meanings. The old
OWNER interpreter and D981 interpreter remain untouched. Unsupported wrappers
are NOT falsely classified pure by this definition; their adequacy is open. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) : State :=
  match s.current.status with
  | .running c => match PV_THR2_Catch316Segment.select c with
    | some _ => PV_LIB_A_OwnerStore.step C K P resources encode H values s
    | none => match select P c with
      | none => PV_LIB_A_OwnerStore.step C K P resources encode H values s
      | some site => deliver C c s.current.world s.current.events s.suspended site
          (H site.waiting.request s.current.world)
  | _ => PV_LIB_A_OwnerStore.step C K P resources encode H values s

/-- Agreement with D981 away from the ELEVEN newly implemented functions. -/
theorem agreement_v1 (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (away : ∀ c, s.current.status = .running c → select P c = none) :
    step C K P resources encode H values s = PV_LIB_A_OwnerStore.step C K P resources encode H values s := by
  unfold step
  cases hs : s.current.status <;> try rfl
  rename_i c
  cases hc : PV_THR2_Catch316Segment.select c <;> simp only [hc,away c hs]

/-- Extended symbolic agreement against the actual OWNER-aware base, retaining
registration, operators, bridged allocations and the identical resource channel.
This is away from ALL implemented old/new actions, not a purity claim for
unimplemented typed destructor/native wrapper effects. -/
theorem agreement_owner (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (awayNew : ∀ c, s.current.status = .running c → select P c = none)
    (awayOld : ∀ c, s.current.status = .running c → PV_THR2_SourceStoreNative.select P c = none) :
    step C K P resources encode H values s =
      PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s :=
  (agreement_v1 C K P resources encode H values s awayNew).trans
    (PV_LIB_A_OwnerStore.agreement C K P resources encode H values s awayOld)

/-- All full replies preserve exact world/events and the suspended stack. -/
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
  unfold deliver
  cases meaning : interpret C site.meaning site.arguments c.store w (H site.waiting.request w) with
  | none => exact ⟨rfl,rfl,rfl⟩
  | some store =>
    have h := PV_THR2_ChildBoundary.effects C {c with store := store} site.waiting
      (H site.waiting.request w)
    exact ⟨h.1,congrArg (es ++ ·) h.2,rfl⟩

#print axioms interpret
#print axioms agreement_v1
#print axioms agreement_owner
#print axioms effects
end PV_LIB_A_StoreDispatchV2
