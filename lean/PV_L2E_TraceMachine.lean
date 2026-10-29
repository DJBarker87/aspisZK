import PV_FIB_Restricted
set_option autoImplicit false
noncomputable section
namespace PV_L2E

/-! TOP-DOWN SKELETON ONLY. `native` must be the deployed small-step machine,
`simulator` must be the simE/D163 coupled replay, and `Related` its source
invariant. These parameters have NOT been instantiated. A step emits an
ordered list, so failed steps and their prefixes are retained. No whole-trace
equality appears in a link. A link is a local forward simulation obligation.
The native/canonical/simE associations remain open, rather than being axioms. -/
inductive Site where
  | v353 | v354 | v355 | v356 | v357 | v358 | v359 | v360
  | v361 | v362 | v363 | v364 | v365 | v367
  deriving DecidableEq

structure Machine (State Event : Type) where
  site : State → Site
  step : State → List Event × State

/-- State relations must cover both normal and stopped states, with a stopped
state emitting [] forever. For divergent runs we compare every finite prefix. -/
def prefix {S E : Type} (m : Machine S E) : Nat → S → List E
  | 0, _ => []
  | n+1, s => let r := m.step s; r.1 ++ prefix m n r.2

/-- A single source transition and its successor invariant, NOT equality of
complete traces. This still needs a statement-by-statement native binding. -/
def StepLink {S T E : Type} (a : Machine S E) (b : Machine T E)
    (Related : S → T → Prop) (site : Site) : Prop :=
  ∀ s t, Related s t → a.site s = site →
    (a.step s).1 = (b.step t).1 ∧ Related (a.step s).2 (b.step t).2

def PV_L2E_Link_V353 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v353
def PV_L2E_Link_V354 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v354
def PV_L2E_Link_V355 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v355
def PV_L2E_Link_V356 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v356
def PV_L2E_Link_V357 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v357
def PV_L2E_Link_V358 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v358
def PV_L2E_Link_V359 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v359
def PV_L2E_Link_V360 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v360
def PV_L2E_Link_V361 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v361
def PV_L2E_Link_V362 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v362
def PV_L2E_Link_V363 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v363
def PV_L2E_Link_V364 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v364
def PV_L2E_Link_V365 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v365
def PV_L2E_Link_V367 {S T E : Type} (a : Machine S E) (b : Machine T E)
    (r : S → T → Prop) : Prop := StepLink a b r .v367

/-- The simulator has only public input and coins; no witness argument. The
initial-invariant premise must be supplied on the SAME good cp.toM sample
as the native cp.toR run, using canonical preparation and D163. It is NOT
currently supplied by RunJoin.agreement (which only relates the view). -/
theorem trace_simulatable {S T E I P C : Type}
    (native : Machine S E) (simulator : Machine T E)
    (Related : S → T → Prop) (good honest : I → Prop)
    (realInit : I → S) (pubData : I → P) (coins : I → C)
    (simInit : P → C → T)
    (initial : ∀ i, honest i → good i →
      Related (realInit i) (simInit (pubData i) (coins i)))
    (v353 : PV_L2E_Link_V353 native simulator Related)
    (v354 : PV_L2E_Link_V354 native simulator Related)
    (v355 : PV_L2E_Link_V355 native simulator Related)
    (v356 : PV_L2E_Link_V356 native simulator Related)
    (v357 : PV_L2E_Link_V357 native simulator Related)
    (v358 : PV_L2E_Link_V358 native simulator Related)
    (v359 : PV_L2E_Link_V359 native simulator Related)
    (v360 : PV_L2E_Link_V360 native simulator Related)
    (v361 : PV_L2E_Link_V361 native simulator Related)
    (v362 : PV_L2E_Link_V362 native simulator Related)
    (v363 : PV_L2E_Link_V363 native simulator Related)
    (v364 : PV_L2E_Link_V364 native simulator Related)
    (v365 : PV_L2E_Link_V365 native simulator Related)
    (v367 : PV_L2E_Link_V367 native simulator Related)
    (i : I) (hi : honest i) (hg : good i) :
    ∀ n, prefix native n (realInit i) =
      prefix simulator n (simInit (pubData i) (coins i)) := by
  have step : ∀ s t, Related s t →
      (native.step s).1 = (simulator.step t).1 ∧
      Related (native.step s).2 (simulator.step t).2 := by
    intro s t h
    cases hs : native.site s
    exacts [v353 s t h hs, v354 s t h hs, v355 s t h hs,
      v356 s t h hs, v357 s t h hs, v358 s t h hs,
      v359 s t h hs, v360 s t h hs, v361 s t h hs,
      v362 s t h hs, v363 s t h hs, v364 s t h hs,
      v365 s t h hs, v367 s t h hs]
  have all : ∀ n s t, Related s t → prefix native n s = prefix simulator n t := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro s t h
      obtain ⟨he, hr⟩ := step s t h
      exact congrArg₂ List.append he (ih _ _ hr)
  exact fun n => all n _ _ (initial i hi hg)

#print axioms trace_simulatable
end PV_L2E
