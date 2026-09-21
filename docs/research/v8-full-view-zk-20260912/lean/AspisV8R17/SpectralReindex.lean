import Mathlib.Logic.Equiv.Defs

/-! Internal spectral coordinate changes cancel in pointwise products and
inverse transport. No FFT laws, field axioms, or privacy premises are used.
The actual bit-reversal permutation and DIF/DIT source correspondence remain
separate obligations; this lemma does not discharge them. -/
set_option autoImplicit false
namespace AspisV8R17.SpectralReindex
variable {I R : Type*} [Mul R]

def reindex (e : I ≃ I) (a : I → R) : I → R := fun i => a (e i)

theorem product (e : I ≃ I) (a b : I → R) :
    reindex e (fun i => a i * b i) =
      (fun i => reindex e a i * reindex e b i) := rfl

theorem unproduct (e : I ≃ I) (a b : I → R) :
    reindex e.symm (fun i => reindex e a i * reindex e b i) =
      (fun i => a i * b i) := by
  funext i
  simp only [reindex, Equiv.apply_symm_apply]

/-- The inverse consumes the permuted spectrum directly; the fixed
multiplier must use the same permutation as the forward output. -/
theorem convolution_pipeline (e : I ≃ I)
    (forward inverse : (I → R) → (I → R)) (a fixedSpectrum : I → R) :
    inverse (reindex e.symm (fun i =>
      reindex e (forward a) i * reindex e fixedSpectrum i)) =
    inverse (fun i => forward a i * fixedSpectrum i) := by
  rw [unproduct]

#print axioms product
#print axioms unproduct
#print axioms convolution_pipeline
end AspisV8R17.SpectralReindex
