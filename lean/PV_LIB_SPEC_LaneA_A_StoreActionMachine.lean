import PV_LIB_SPEC_LaneA_A_StoreActionTable
set_option autoImplicit false
noncomputable section
namespace PV_LIB_StoreActionTable
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
abbrev State := PV_LIB_A_OwnerStore.State
abbrev Handler := PV_LIB_A_OwnerStore.Handler

structure Site where
  action : Action
  callee : Data
  waiting : PV_STX2_Native.Waiting Data
  arguments : List Data

/-- Inline bodies are expanded by the OWNER base. The table is used only for
an actual native poll, so nested atomics are not applied again to an inline
Arc body. Catch316 interception retains its existing priority. -/
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
        let action ← v2 fn
        pure ⟨action,fn,wait,args⟩
    | _ => none

def deliver (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent)
    (stack : List Config) (site : Site) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) : State :=
  match interpret C values site.action site.callee site.arguments c.store w r with
  | none => ⟨⟨.undefined none c.store,r.world,es ++ r.events⟩,stack⟩
  | some store =>
    let q := PV_THR2_ChildBoundary.delivered C {c with store := store} site.waiting r
    ⟨⟨q.status,q.world,es ++ q.events⟩,stack⟩

/-- One dispatch layer on the unchanged OWNER-aware interpreter. It is a
partial source-semantics candidate, as the table's coverage records explicitly.
This definition is not a MachineSpec adequacy assertion. -/
def step (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State) : State :=
  match s.current.status with
  | .running c => match PV_THR2_Catch316Segment.select c with
    | some _ => PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s
    | none => match select P c with
      | none => PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s
      | some site => deliver C values c s.current.world s.current.events s.suspended site
          (H site.waiting.request s.current.world)
  | _ => PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s

def Neutral (P : Data → Option PV_STX2_SliceSyntax.Program) (s : State) : Prop :=
  ∀ c, s.current.status = .running c → select P c = none

/-- Single symbolic agreement lemma against the OWNER-aware base, with the
identical resource environment, registration, operators and allocation actions.
Away from supplied entries is not a no-write theorem for missing entries. -/
theorem agreement (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (s : State)
    (away : Neutral P s) :
    step C K P resources encode H values s =
      PV_THR2_OwnInitInterpreterBridged.step C K P resources encode H s := by
  unfold step
  cases hs : s.current.status <;> try rfl
  rename_i c
  cases hc : PV_THR2_Catch316Segment.select c <;> simp only [hc,away c hs]

/-- Exact all-answer graph at an action. There is no successful-answer or
write-definedness premise. `deliver` exposes its unsupported/undefined arm;
this theorem does not silently turn that arm into a source execution. -/
theorem native (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : Site) (ordinary : PV_THR2_Catch316Segment.select c = none)
    (selected : select P c = some site) :
    step C K P resources encode H values ⟨⟨.running c,w,es⟩,stack⟩ =
      deliver C values c w es stack site (H site.waiting.request w) := by
  simp only [step,ordinary,selected]

theorem effects (C : Carrier OWNER Data) (values : Values OWNER PV_RJ4IDB.NativeEvent)
    (c : Config) (w : OWNER) (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (site : Site) (r : Reply OWNER PV_RJ4IDB.NativeEvent Data) :
    let out := deliver C values c w es stack site r
    out.current.world = r.world ∧ out.current.events = es ++ r.events ∧ out.suspended = stack := by
  simp only [deliver]
  cases meaning : interpret C values site.action site.callee site.arguments c.store w r with
  | none => exact ⟨rfl,rfl,rfl⟩
  | some store =>
    have h := PV_THR2_ChildBoundary.effects C {c with store := store} site.waiting r
    exact ⟨h.1,congrArg (es ++ ·) h.2,rfl⟩

def advance (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) : Nat → State → State
  | 0,s => s
  | n+1,s => advance C K P resources encode H values n (step C K P resources encode H values s)

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

#print axioms select
#print axioms deliver
#print axioms step
#print axioms agreement
#print axioms native
#print axioms effects
#print axioms advance_agreement
end PV_LIB_StoreActionTable
