import PV_THR2_IntrinsicFrameAggregate
import PV_THR2_IntrinsicFrameBind
import PV_THR2_IntrinsicFrameSteps
set_option autoImplicit false
namespace PV_FN_W4_OwnChain
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Finite source instruction certificate; all store-dependent binding failures stay. -/
inductive Chain where
  | done
  | storage (site : Site) (live : Bool) (slot : Nat) (next : Chain)
  | bind (site : Site) (dest : Place) (expr : Expr) (next : Chain)
  | aggregate (site : Site) (dest : Place) (kind : Data) (args : List Operand) (next : Chain)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Certificate source nodes, with an arbitrary real following continuation. -/
def nodes : Chain → List PV_STX2_SliceSyntax.Node
  | .done => []
  | .storage site live slot next => .leaf (.storage site live slot) :: nodes next
  | .bind site dest expr next => .leaf (.bind site dest expr) :: nodes next
  | .aggregate site dest kind args next => .leaf (.aggregateMove site dest kind args) :: nodes next
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Binding outcome of the unchanged interpreter, including aggregate fallback. -/
def bound {W : Type} (base : Carrier W Data) (s : Store Data) (a : Nat)
    (dest : Place) (expr : Expr) (w : W) :=
  (PV_STX2_Store.bind base s w a dest expr).orElse
    (fun _ => PV_STX2_Store.bind (PV_THR2_AggregateCompletion.carrier base) s w a dest expr)
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Finite administrative fuel stops at the first missing binding. -/
def steps {W : Type} (base : Carrier W Data) (a : Nat) (w : W) : Chain → Store Data → Nat
  | .done,_ => 0
  | .storage _ _ slot next,s => 1 + steps base a w next (write s ⟨a,slot,[]⟩ none)
  | .bind _ dest expr next,s => 1 + match bound base s a dest expr w with
      | none => 0 | some t => steps base a w next t
  | .aggregate _ dest kind args next,s => 1 + match bound base s a dest (.aggregate kind args) w with
      | none => 0 | some t => steps base a w next t
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Exact symbolic store effects; failed bindings retain their own generated site. -/
def result {W : Type} (base : Carrier W Data) (a : Nat) (parents : List Frame)
    (loops : List LoopFrame) (rest : List PV_STX2_SliceSyntax.Node) (w : W) : Chain → Store Data → Status
  | .done,s => .running ⟨{activation := a,remaining := rest,loops := loops},parents,s⟩
  | .storage _ _ slot next,s => result base a parents loops rest w next (write s ⟨a,slot,[]⟩ none)
  | .bind site dest expr next,s => match bound base s a dest expr w with
      | none => .undefined (some site) s
      | some t => result base a parents loops rest w next t
  | .aggregate site dest kind args next,s => match bound base s a dest (.aggregate kind args) w with
      | none => .undefined (some site) s
      | some t => result base a parents loops rest w next t
/-- Conditional on owner acceptance of amended translator. Hypotheses: none.
Compose a finite certificate by named single-frame steps, without store reduction. -/
theorem run {W E : Type} (base : Carrier W Data) (ctl : Control)
    (programs : Data → Option PV_STX2_SliceSyntax.Program)
    (handler : PV_STX2_Native.Request Data → W → Reply W E Data)
    (chain : Chain) (s : Store Data) (a : Nat) (parents : List Frame) (loops : List LoopFrame)
    (rest : List PV_STX2_SliceSyntax.Node) (w : W) (es : List E) (stack : List Config) :
    PV_THR2_IntrinsicState.advance base ctl programs handler (steps base a w chain s)
      ⟨⟨.running ⟨{activation := a,remaining := nodes chain ++ rest,loops := loops},parents,s⟩,w,es⟩,stack⟩ =
      ⟨⟨result base a parents loops rest w chain s,w,es⟩,stack⟩ := by
  induction chain generalizing s with
  | done => rfl
  | storage site live slot next ih =>
    simp only [steps,nodes,List.cons_append]
    rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicFrameSteps.storage]
    exact ih _
  | bind site dest expr next ih =>
    simp only [steps,nodes,List.cons_append]
    rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicFrameBind.run]
    unfold PV_THR2_IntrinsicFrameBind.after
    change PV_THR2_IntrinsicState.advance base ctl programs handler (match bound base s a dest expr w with | none => 0 | some t => steps base a w next t)
      (match bound base s a dest expr w with
       | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
       | some t => ⟨⟨.running ⟨{activation := a,remaining := nodes next ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩) = _
    cases hb : bound base s a dest expr w with
    | none => simp only [result,hb]; rfl
    | some t => simpa only [result,hb] using ih t
  | aggregate site dest kind args next ih =>
    simp only [steps,nodes,List.cons_append]
    rw [PV_THR2_IntrinsicComposition.advance_add,PV_THR2_IntrinsicFrameAggregate.run]
    unfold PV_THR2_IntrinsicFrameAggregate.after
    change PV_THR2_IntrinsicState.advance base ctl programs handler (match bound base s a dest (.aggregate kind args) w with | none => 0 | some t => steps base a w next t)
      (match bound base s a dest (.aggregate kind args) w with
       | none => ⟨⟨.undefined (some site) s,w,es⟩,stack⟩
       | some t => ⟨⟨.running ⟨{activation := a,remaining := nodes next ++ rest,loops := loops},parents,t⟩,w,es⟩,stack⟩) = _
    cases hb : bound base s a dest (.aggregate kind args) w with
    | none => simp only [result,hb]; rfl
    | some t => simpa only [result,hb] using ih t
#print axioms run
end PV_FN_W4_OwnChain
