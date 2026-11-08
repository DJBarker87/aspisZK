import PV_LIB_A_SourceWriters
import PV_THR2_OwnInitInterpreterBridged
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_OwnerStore
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_THR2_SourceStoreNative PV_THR2_SourceStoreLibrary
abbrev State := PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent
abbrev Handler := PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data
/-- D981: extend the OWNER-aware bridged interpreter, retaining its registration,
operators, allocations and intrinsic actions on every other configuration.
The five source meanings are W4's definitions, never a supplied Store action. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) : State :=
  match s.current.status with
  | .running c => match PV_THR2_Catch316Segment.select c with
    | some _ => PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s
    | none => match select P c with
      | none => PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s
      | some site => PV_LIB_A_SourceWriters.internalModel C values c s.current.world
          s.current.events s.suspended site (H site.waiting.request s.current.world)
  | _ => PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s

def advance (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) : Nat → State → State
  | 0,s => s
  | n+1,s => advance C K P resources encode H values n (step C K P resources encode H values s)

/-- Agreement is against the OWNER-aware step, not IntrinsicState.step. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (away : ∀ c, s.current.status = .running c → select P c = none) :
    step C K P resources encode H values s =
      PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s := by
  unfold step
  cases hs : s.current.status <;> try rfl
  rename_i c
  cases hc : PV_THR2_Catch316Segment.select c <;> simp only [hc,away c hs]

/-- The deterministic writer graph is now installed on the corrected machine.
No successful-answer, valid-write or identity-effect hypothesis is introduced. -/
theorem installed (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : PV_THR2_SourceStoreNative.Site) (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select P c = some site) :
    PV_LIB_A_SourceWriters.law C values c w es stack site (H site.waiting.request w)
      (PV_LIB.observe (step C K P resources encode H values ⟨⟨.running c,w,es⟩,stack⟩)) := by
  unfold step
  simp only [ordinary,selected]
  rfl

/-- Every world, event suffix and suspended frame survives every native answer,
including malformed layout (undefined), pending, failure, abort and divergence. -/
theorem effects (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : PV_THR2_SourceStoreNative.Site) (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select P c = some site) :
    let r := H site.waiting.request w
    let out := step C K P resources encode H values ⟨⟨.running c,w,es⟩,stack⟩
    out.current.world = r.world ∧ out.current.events = es ++ r.events ∧ out.suspended = stack := by
  simp only [step,ordinary,selected]
  change (PV_LIB_A_SourceWriters.internalModel C values c w es stack site
    (H site.waiting.request w)).current.world = _ ∧ _
  unfold PV_LIB_A_SourceWriters.internalModel
  cases meaning : interpret C values site.meaning site.callee site.arguments c.store w
      (H site.waiting.request w) with
  | none => exact ⟨rfl,rfl,rfl⟩
  | some store =>
    have h := PV_THR2_ChildBoundary.effects C {c with store := store}
      site.waiting (H site.waiting.request w)
    exact ⟨h.1,congrArg (es ++ ·) h.2,rfl⟩
#print axioms agreement
#print axioms installed
#print axioms effects
end PV_LIB_A_OwnerStore
