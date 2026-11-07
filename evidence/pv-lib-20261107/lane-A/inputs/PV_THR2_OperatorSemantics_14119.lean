import PV_THR2_IntrinsicFrameBind
import PV_THR2_OwnInitFieldCodec
import PV_THR2_F361
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OperatorSemantics_14119
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open scoped Classical
/-- Conditional on amended-translator acceptance. Thread15/D856, Recount14:
F361.node133/14119 is Unsize thin39233 to dyn raw39257/39258, VTable impl115,
hash-consed39260; NOT an identity cast. Exact N95807 metadata in
session93/live-cast-metadata.json.xz. nightly-2026-06-01,
rustc14210df0e27ccd7d9e6a05b8085cbd438e4bbc65.
https://doc.rust-lang.org/reference/type-coercions.html#unsized-coercions
https://doc.rust-lang.org/reference/types/trait-object.html
The vtable address is a named linkage constant, opaque in value. The theorem
is uniform in that constant; no address, validity or endpoint fact is assumed. -/
def token : Data := match PV_THR2_F361.node133 with
  | .leaf (.bind _ _ (.unary op _)) => op | _ => .null
/-- Symbol environment for the exact emitted impl115 vtable. An arbitrary
ELF64 address, fixed for the whole run; never guessed or selected for ownership. -/
structure Symbols where
  vtable_115 : PV_OWN2_Codec.Pointer
/-- The named constant's representation, independent of operand and world. -/
def vtable_115 (symbols : Symbols) : Data :=
  PV_THR2_OwnInitPointerCodec.encode symbols.vtable_115
/-- Raw dyn pointer representation: data first, vtable metadata second. -/
def fat (data metadata : Data) : Data := .array [data,metadata]
def result (symbols : Symbols) (operand : Data) : Data :=
  fat operand (vtable_115 symbols)
/-- Hypotheses: none. Exact thin-to-fat semantics, preserving the data part. -/
theorem representation (symbols : Symbols) (v : Data) :
    result symbols v = fat v (vtable_115 symbols) := rfl
/-- Hypotheses: none. Exact inverse-compatible two-word callback representation. -/
theorem callback (symbols : Symbols) (p : PV_OWN2_Codec.Pointer) :
    result symbols (PV_THR2_OwnInitPointerCodec.encode p) =
      PV_THR2_OwnInitFieldCodec.callback p symbols.vtable_115 := rfl
/-- Exact token only; every other operation retains its original meaning. -/
def carrier {W : Type} (symbols : Symbols) (base : Carrier W Data) : Carrier W Data :=
  {base with unary := fun op v => if op = token then some (result symbols v) else base.unary op v}
/-- Hypotheses: none. Install the named documented-semantics fact. -/
theorem installed {W : Type} (symbols : Symbols) (base : Carrier W Data) (v : Data) :
    (carrier symbols base).unary token v = some (fat v (vtable_115 symbols)) := by simp only [carrier,ite_true,result]
/-- Symbolic slice3 value agreement outside the exact new token. -/
theorem away {W : Type} (symbols : Symbols) (base : Carrier W Data) (op v : Data) (h : op ≠ token) :
    (carrier symbols base).unary op v = base.unary op v := by simp only [carrier,if_neg h]
/-- The new action selector is instruction shape alone, independent of stores. -/
def selected (s : Status) : Prop := ∃ c site dest operand rest,
  s = .running c ∧ c.frame.waiting = none ∧ c.frame.unwinding = none ∧
  c.frame.remaining = .leaf (.bind site dest (.unary token operand)) :: rest
/-- NEW interpreter extension, leaving the retained interpreter untouched. -/
def step {W E : Type} (symbols : Symbols) (base : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : PV_THR2_IntrinsicState.State W E) :=
  if selected s.current.status then PV_THR2_IntrinsicState.step (carrier symbols base) K P H s
  else PV_THR2_IntrinsicState.step base K P H s
/-- ONE symbolic slice3 step agreement on every configuration away from14119.
Hypothesis is instruction shape, never a run/endpoint premise. -/
theorem agreement {W E : Type} (symbols : Symbols) (base : Carrier W Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (H : PV_STX2_Native.Request Data → W → Reply W E Data)
    (s : PV_THR2_IntrinsicState.State W E) (h : ¬ selected s.current.status) :
    step symbols base K P H s = PV_THR2_IntrinsicState.step base K P H s := by
  simp only [step,if_neg h]
#print axioms representation
#print axioms callback
#print axioms installed
#print axioms away
#print axioms agreement
end PV_THR2_OperatorSemantics_14119
/-- Exact named operator semantics; no hypothesis or trust axiom. -/
def PV_THR2_OperatorSemantics_14119 := PV_THR2_OperatorSemantics_14119.result
