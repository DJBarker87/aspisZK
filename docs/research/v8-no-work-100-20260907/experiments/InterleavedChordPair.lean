import InterleavedChordAlgebra
import NaturalChordImage

/-! Smallest selected coefficient-pair interface, isolated from transpose,
matrix projection and row composition. Synchronous elaboration and reduced
limits expose any concrete conversion before a larger bridge is compiled. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 80
set_option maxHeartbeats 2000
namespace AspisV8.InterleavedChordRows
noncomputable section
open Polynomial AspisV5FriInitialCircleEncoderIdentity
open AspisV8.NaturalChordImage AspisV8.InterleavedChordLinear
variable {K : Type*} [Field K] [NeZero (2 : K)] [DecidableEq K]

def evenPolynomial : (Fin 1024 → K) →ₗ[K] K[X] :=
  (lineLinear 512).comp (evenLinear 512)
def oddPolynomial : (Fin 1024 → K) →ₗ[K] K[X] :=
  (lineLinear 512).comp (oddLinear 512)

theorem evenPolynomial_apply (q : Fin 1024 → K) : evenPolynomial q=line (even q) := by
  unfold evenPolynomial
  rw [LinearMap.comp_apply,lineLinear_apply,evenLinear_apply]
  congr 1
theorem oddPolynomial_apply (q : Fin 1024 → K) : oddPolynomial q=line (odd q) := by
  unfold oddPolynomial
  rw [LinearMap.comp_apply,lineLinear_apply,oddLinear_apply]
  congr 1

#print axioms evenPolynomial_apply
#print axioms oddPolynomial_apply
end
end AspisV8.InterleavedChordRows
