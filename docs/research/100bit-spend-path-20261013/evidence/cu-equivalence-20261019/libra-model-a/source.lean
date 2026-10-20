import CuSavingsLibraSourceBuilder
import CuSavingsLibraProgram

/-! Local arithmetic refinement interface consumed by source-loop induction.
This is a structure of hypotheses, not an axiom or final equivalence result.
The production instance must discharge these fields using actual extracted
canonical arithmetic; no instance is postulated here. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourceModel
open Aeneas Aeneas.Std Result AspisR1Libra
abbrev E := field.wide_exact.WideExact
abbrev K := field.QM31

structure Arithmetic (R S : Type) [CommSemiring R] [CommSemiring S] [Shared] where
  canonicalE : E → Prop
  canonicalK : K → Prop
  decodeE : E → R
  decodeK : K → S
  embedding : S →+* R
  quarter : R
  zero : canonicalE field.wide_exact.WideExact.ZERO
  zero_value : decodeE field.wide_exact.WideExact.ZERO=0
  one : canonicalK field.QM31.ONE
  one_value : decodeK field.QM31.ONE=1
  add : ∀ a b, canonicalE a → canonicalE b → ∃ out,
    field.wide_exact.WideExact.add a b=.ok out ∧ canonicalE out ∧ decodeE out=decodeE a+decodeE b
  mul : ∀ a b, canonicalE a → canonicalE b → ∃ out,
    field.wide_exact.WideExact.mul a b=.ok out ∧ canonicalE out ∧ decodeE out=decodeE a*decodeE b
  mixed : ∀ a q, canonicalE a → canonicalK q → ∃ out,
    field.wide_exact.WideExact.mul_qm31 a q=.ok out ∧ canonicalE out ∧
      decodeE out=decodeE a*embedding (decodeK q)
  scalar : ∀ a, canonicalE a → ∃ out,
    field.wide_exact.WideExact.mul_m31 a QUARTER=.ok out ∧ canonicalE out ∧
      decodeE out=decodeE a*quarter
  kmul : ∀ a b, canonicalK a → canonicalK b → ∃ out,
    field.QM31.mul a b=.ok out ∧ canonicalK out ∧ decodeK out=decodeK a*decodeK b
  square : ∀ a, canonicalK a → ∃ out,
    field.QM31.square a=.ok out ∧ canonicalK out ∧ decodeK out=(decodeK a)^2
  injective : ∀ a b, canonicalE a → canonicalE b → decodeE a=decodeE b → a=b

#print axioms Arithmetic
end AspisR1.CuSavingsLibraSourceModel
