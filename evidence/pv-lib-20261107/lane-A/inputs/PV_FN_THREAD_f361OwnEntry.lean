import PV_FN_THREAD_f361JoinStatements
import PV_THR2_OperatorNeutral
import PV_THR2_OwnUniformNeutral
import PV_FN_THREAD_SourceChainFrame
set_option autoImplicit false
noncomputable section
namespace PV_FN_THREAD_f361OwnEntry
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_FN_THREAD_f361 PV_THR2_IntrinsicFrameChain

/-- Concatenate finite certificates without resetting any intervening store. -/
def append {x : Input} {q r out : State} (first : Run x q r)
    (second : Run x r out) : Run x q out :=
  match first with
  | .refl _ => second
  | .source q r _ h stepEq tail => .source q r out h stepEq (append tail second)
  | .native q r _ e call leaf callback initEq post resultEq tail =>
      .native q r out e call leaf callback initEq post resultEq (append tail second)
  | .callback q r _ e call functionEq resultEq tail =>
      .callback q r out e call functionEq resultEq (append tail second)
  | .initAllocation q r _ e call functionEq resultEq tail =>
      .initAllocation q r out e call functionEq resultEq (append tail second)
  | .body q r _ e call summary tail => .body q r out e call summary (append tail second)
  | .drop q r _ c site slot fn conditional rest value running activation waiting unwinding
      shape cell resultEq tail =>
      .drop q r out c site slot fn conditional rest value running activation waiting unwinding
        shape cell resultEq (append tail second)

/-- Three already proved symbolic neutrality laws, at THIS source state.
These local shape conditions are discharged from the chain, not row premises. -/
theorem ordinary (x : Input) (q : State)
    (allocation : ∀ c, q.current.status = .running c → PV_THR2_OwnInitAction.selected c = false)
    (operator : ∀ c, q.current.status = .running c → PV_THR2_OperatorNeutral.configuration c)
    (registration : ∀ c, q.current.status = .running c → PV_THR2_OwnUniformNeutral.configuration c) :
    PV_THR2_OwnInitInterpreterBridged.step (base x) x.K (fun _ => none)
      x.resources x.encode (handler x) q =
      PV_THR2_IntrinsicState.step (base x) x.K (fun _ => none) (handler x) q :=
  (PV_THR2_OwnInitInterpreterBridged.agreement _ _ _ _ _ _ q allocation).trans
    ((PV_THR2_OperatorNeutral.step _ _ _ _ q operator).trans
      (PV_THR2_OwnUniformNeutral.step _ _ _ _ q registration))

def state (x : Input) (s : Store Data) (parents : List Frame) (loops : List LoopFrame)
    (nodes : List PV_STX2_SliceSyntax.Node) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) : State :=
  ⟨⟨.running ⟨{activation := x.a,remaining := nodes,loops := loops},parents,s⟩,w,es⟩,stack⟩

/-- The finite source prefix excludes only the named action shapes.
No operand evaluation or successful native reply is part of this predicate. -/
def Plain : Chain → Prop
  | .done => True
  | .storage site live slot next =>
      PV_THR2_OwnUniformNeutral.instruction (.storage site live slot) ∧ Plain next
  | .bind site dest expr next =>
      PV_THR2_OperatorAction.instruction (.bind site dest expr) = none ∧ Plain next

theorem storage_step (x : Input) (s : Store Data) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (site : Site) (live : Bool) (slot : Nat) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (neutral : PV_THR2_OwnUniformNeutral.instruction (.storage site live slot)) :
    PV_THR2_OwnInitInterpreterBridged.step (base x) x.K (fun _ => none)
      x.resources x.encode (handler x)
      (state x s parents loops (.leaf (.storage site live slot) :: rest) w es stack) =
      state x (write s ⟨x.a,slot,[]⟩ none) parents loops rest w es stack := by
  let q := state x s parents loops (.leaf (.storage site live slot) :: rest) w es stack
  have lifted := ordinary x q (by intro c h; cases h; rfl)
    (by intro c h; cases h; rfl) (by intro c h; cases h; exact neutral)
  have core := PV_THR2_IntrinsicFrameSteps.storage (base x) x.K (fun _ => none)
    (handler x) s x.a parents loops rest site live slot w es stack
  exact lifted.trans core

theorem bind_step (x : Input) (s : Store Data) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (site : Site) (dest : PV_STX2_Syntax.Place) (expr : Expr) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config)
    (neutral : PV_THR2_OperatorAction.instruction (.bind site dest expr) = none) :
    PV_THR2_OwnInitInterpreterBridged.step (base x) x.K (fun _ => none)
      x.resources x.encode (handler x)
      (state x s parents loops (.leaf (.bind site dest expr) :: rest) w es stack) =
      PV_THR2_IntrinsicFrameBind.after (base x) s x.a parents loops rest site dest expr w es stack := by
  let q := state x s parents loops (.leaf (.bind site dest expr) :: rest) w es stack
  have lifted := ordinary x q (by intro c h; cases h; rfl)
    (by intro c h; cases h; exact neutral) (by intro c h; cases h; trivial)
  have core := PV_THR2_IntrinsicFrameBind.run (base x) x.K (fun _ => none)
    (handler x) s x.a parents loops rest site dest expr w es stack
  exact lifted.trans core

theorem sourceOnly_storage (x : Input) (s : Store Data) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (site : Site) (live : Bool) (slot : Nat) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    SourceOnly x (state x s parents loops (.leaf (.storage site live slot) :: rest) w es stack) := by
  intro c h
  cases h
  refine ⟨rfl,rfl,?_,?_⟩
  · intro site fn args dest cleanup tail impossible
    cases impossible
  · intro site slot fn conditional cleanup tail impossible
    cases impossible

theorem sourceOnly_bind (x : Input) (s : Store Data) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node)
    (site : Site) (dest : PV_STX2_Syntax.Place) (expr : Expr) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :
    SourceOnly x (state x s parents loops (.leaf (.bind site dest expr) :: rest) w es stack) := by
  intro c h
  cases h
  refine ⟨rfl,rfl,?_,?_⟩
  · intro site fn args dest cleanup tail impossible
    cases impossible
  · intro site slot fn conditional cleanup tail impossible
    cases impossible

/-- Lift the EXISTING chain result into a full-store caller certificate.
Each transition is the named storage/bind theorem; no callee is traversed. -/
theorem chain (x : Input) (source : Chain) (s : Store Data) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) (plain : Plain source) :
    Execution x (state x s parents loops (nodes source ++ rest) w es stack)
      ⟨⟨result (base x) x.a parents loops rest w source s,w,es⟩,stack⟩ := by
  induction source generalizing s with
  | done => exact ⟨.refl _⟩
  | storage site live slot next ih =>
    obtain ⟨tail⟩ := ih (write s ⟨x.a,slot,[]⟩ none) plain.2
    exact ⟨.source _ _ _
      (sourceOnly_storage x s parents loops (nodes next ++ rest) site live slot w es stack)
      (storage_step x s parents loops (nodes next ++ rest) site live slot w es stack plain.1) tail⟩
  | bind site dest expr next ih =>
    have step := bind_step x s parents loops (nodes next ++ rest) site dest expr w es stack plain.1
    unfold PV_THR2_IntrinsicFrameBind.after at step
    change PV_THR2_OwnInitInterpreterBridged.step (base x) x.K (fun _ => none)
      x.resources x.encode (handler x) _ =
      (match bound (base x) s x.a dest expr w with
      | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
      | some t => state x t parents loops (nodes next ++ rest) w es stack) at step
    cases hb : bound (base x) s x.a dest expr w with
    | none =>
      simp only [hb] at step
      refine ⟨.source _ _ _
        (sourceOnly_bind x s parents loops (nodes next ++ rest) site dest expr w es stack) step ?_⟩
      simpa only [result,hb] using (Run.refl (x := x) ⟨⟨.undefined (some site) s,w,es⟩,stack⟩)
    | some t =>
      simp only [hb] at step
      obtain ⟨tail⟩ := ih t plain.2
      refine ⟨.source _ _ _
        (sourceOnly_bind x s parents loops (nodes next ++ rest) site dest expr w es stack) step ?_⟩
      simpa only [result,hb] using tail

#print axioms append
#print axioms ordinary
#print axioms storage_step
#print axioms bind_step
#print axioms sourceOnly_storage
#print axioms sourceOnly_bind
#print axioms chain
end PV_FN_THREAD_f361OwnEntry
