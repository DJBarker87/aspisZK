import PV_THR2_IntrinsicFrameBind
import PV_THR2_F361
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OperatorSemantics_14121
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open scoped Classical
/-- Conditional on amended-translator acceptance. Thread15/D856 documented
semantics, Recount14: F361.node135, statement14121, Cast.Transmute33597 to
RawPtr DynTrait39265/39266. N95807 source and metadata are pinned in
session93/live-cast-metadata.json.xz. nightly-2026-06-01,
rustc14210df0e27ccd7d9e6a05b8085cbd438e4bbc65.
https://doc.rust-lang.org/std/mem/fn.transmute.html (bitwise move between
same-size types). No native parity, validity or allocation claim. -/
def token : Data := match PV_THR2_F361.node135 with
  | .leaf (.bind _ _ (.unary op _)) => op | _ => .null
def result (operand : Data) : Data := operand
/-- Hypotheses: none. Exact represented value, bytes and place preserved. -/
theorem representation {W B : Type} (base : Carrier W Data) (w : W)
    (bytes : Data → B) (v : Data) :
    result v = v ∧ bytes (result v) = bytes v ∧
      base.dereference w (result v) = base.dereference w v := ⟨rfl,rfl,rfl⟩
/-- Exact token only; every other operation retains its original meaning. -/
def carrier {W : Type} (base : Carrier W Data) : Carrier W Data :=
  {base with unary := fun op v => if op = token then some (result v) else base.unary op v}
/-- Hypotheses: none. Install the named documented-semantics fact. -/
theorem installed {W : Type} (base : Carrier W Data) (v : Data) :
    (carrier base).unary token v = some v := by simp only [carrier,ite_true,result]
/-- Symbolic slice3 value agreement outside the exact new token. -/
theorem away {W : Type} (base : Carrier W Data) (op v : Data) (h : op ≠ token) :
    (carrier base).unary op v = base.unary op v := by simp only [carrier,if_neg h]
/-- The new action selector is instruction shape alone, independent of stores. -/
def selected (s : Status) : Prop := ∃ c site dest operand rest,
  s = .running c ∧ c.frame.waiting = none ∧ c.frame.unwinding = none ∧
  c.frame.remaining = .leaf (.bind site dest (.unary token operand)) :: rest
/-- NEW interpreter extension, leaving the retained interpreter untouched. -/
def step {W E : Type} (base : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : PV_THR2_IntrinsicState.State W E) :=
  if selected s.current.status then PV_THR2_IntrinsicState.step (carrier base) K P H s
  else PV_THR2_IntrinsicState.step base K P H s
/-- ONE symbolic slice3 step agreement on every configuration away from14121.
Hypothesis is instruction shape, never a run/endpoint premise. -/
theorem agreement {W E : Type} (base : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : PV_THR2_IntrinsicState.State W E) (h : ¬ selected s.current.status) :
    step base K P H s = PV_THR2_IntrinsicState.step base K P H s := by
  simp only [step,if_neg h]
#print axioms representation
#print axioms installed
#print axioms away
#print axioms agreement
end PV_THR2_OperatorSemantics_14121
/-- Exact named operator semantics; no hypothesis or trust axiom. -/
def PV_THR2_OperatorSemantics_14121 := PV_THR2_OperatorSemantics_14121.result
