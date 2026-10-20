import AspisR1RetainedClaimBinding.Types
import CuSavingsCanonicalVectorContexts
import CuSavingsWideCore
set_option autoImplicit false
namespace AspisR1RetainedClaimBinding
open Aeneas Aeneas.Std Result
abbrev E := field.wide_exact.WideExact
abbrev I := AspisR1CanonicalInputs.field.wide_exact.WideExact
abbrev W := AspisR1WideArithmetic.field.wide_exact.WideExact
class DotCall where
  dot : Usize→Array E 29#usize→Result (core.result.Result E Error)
class Trace where
  value : U8→Usize→E→Result Unit
abbrev claim_dot [DotCall] := DotCall.dot
abbrev trace_value [Trace] := Trace.value
def toInput (x : E) : I :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def fromInput (x : I) : E := AspisR1.CuSavingsCanonicalDotsSources.inputToDot x
def toWide (x : E) : W := AspisR1CanonicalInputs.toE (toInput x)
def fromWide (x : W) : E := fromInput (AspisR1CanonicalInputs.fromE x)
def field.wide_exact.WideExact.add (x y : E) : Result E := do
  let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.add (toWide x) (toWide y)
  .ok (fromWide z)
def field.wide_exact.WideExact.mul (x y : E) : Result E := do
  let z ← AspisR1WideArithmetic.field.wide_exact.WideExact.mul (toWide x) (toWide y)
  .ok (fromWide z)
def powers (N : Usize) (x : E) : Result (Array E N) := do
  let xs ← AspisR1CanonicalInputs.weights.powers N (toInput x)
  .ok ⟨xs.val.map fromInput,by simp only [List.length_map,xs.property]⟩
#print axioms field.wide_exact.WideExact.add
#print axioms powers
end AspisR1RetainedClaimBinding
