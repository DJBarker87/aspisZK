import InterleavedChordLinear

/-! Symbolic polynomial/linear-map algebra before substituting a 512-term
natural polynomial. This avoids normalization of concrete finite sums. -/
set_option autoImplicit false
set_option maxRecDepth 200
namespace AspisV8.InterleavedChordLinear
noncomputable section
open Polynomial AspisV8.NaturalChordImage AspisV8.ChordPolynomialImage
open AspisV5FriInitialCircleEncoderIdentity
variable {K V : Type*} [Field K] [NeZero (2 : K)]

theorem lineLinear_apply {n : Nat} (v : Fin n → K) : lineLinear n v=line v := rfl
theorem evenLinear_apply {n : Nat} (v : Fin (2*n) → K) :
    evenLinear n v=evenCoefficients v := rfl
theorem oddLinear_apply {n : Nat} (v : Fin (2*n) → K) :
    oddLinear n v=oddCoefficients v := rfl

variable [AddCommGroup V] [Module K V]
theorem even_linear_formula (a b c : K) (A B : V →ₗ[K] K[X]) (v : V) :
    ((LinearMap.mulLeft K (C a+C b*X)).comp A +
      (LinearMap.mulLeft K (C c*(1-X^2))).comp B) v =
      evenPart a b c (A v) (B v) := by
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  unfold evenPart
  ring
theorem odd_linear_formula (a b c : K) (A B : V →ₗ[K] K[X]) (v : V) :
    ((LinearMap.mulLeft K (C c)).comp A +
      (LinearMap.mulLeft K (C a+C b*X)).comp B) v =
      oddPart a b c (A v) (B v) := by
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  unfold oddPart
  ring

#print axioms even_linear_formula
#print axioms odd_linear_formula
end
end AspisV8.InterleavedChordLinear
