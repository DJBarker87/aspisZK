import AspisV8R16.FibreInterpolation
import AspisV8R16.NaturalBasisCore

/-! Deterministic coverage in the actual natural line basis. This says
nothing about a posterior after other transcript observations. -/
set_option autoImplicit false
namespace AspisV8R16
open AspisCircleTensorBinding
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem natural_eval_surjective {n : ℕ} (t : Fin n → F)
    (ht : Function.Injective t) :
    Function.Surjective (naturalEvalMatrix F n t).mulVec := by
  intro v
  refine ⟨(monomialToNatural F n * (Matrix.vandermonde t)⁻¹).mulVec v, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    naturalEval_mul_monomialToNatural]
  change (Matrix.vandermonde t * (Matrix.vandermonde t)⁻¹).mulVec v = v
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr
    (Matrix.det_vandermonde_ne_zero_iff.mpr ht)), Matrix.one_mulVec]

/-- Four natural-basis coefficient channels cover arbitrary four-slot
values on every injective fibre-root schedule. At n=22 there are 88
coefficients; no schedule-frequency or extra hiding premise is used. -/
theorem natural_four_slot_coverage {n : ℕ} (t x y v0 v1 v2 v3 : Fin n → F)
    (ht : Function.Injective t) (h4 : (4 : F) ≠ 0)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) :
    ∃ a b c d : Fin n → F,
      let ev := (naturalEvalMatrix F n t).mulVec
      ∀ i,
        ev a i + ev b i*y i + ev c i*x i + ev d i*x i*y i = v0 i ∧
        ev a i - ev b i*y i + ev c i*x i - ev d i*x i*y i = v1 i ∧
        ev a i - ev b i*y i - ev c i*x i + ev d i*x i*y i = v2 i ∧
        ev a i + ev b i*y i - ev c i*x i - ev d i*x i*y i = v3 i := by
  obtain ⟨a, ea⟩ := natural_eval_surjective t ht
    (fun i => splitA (v0 i) (v1 i) (v2 i) (v3 i))
  obtain ⟨b, eb⟩ := natural_eval_surjective t ht
    (fun i => splitB (y i) (v0 i) (v1 i) (v2 i) (v3 i))
  obtain ⟨c, ec⟩ := natural_eval_surjective t ht
    (fun i => splitC (x i) (v0 i) (v1 i) (v2 i) (v3 i))
  obtain ⟨d, ed⟩ := natural_eval_surjective t ht
    (fun i => splitD (x i) (y i) (v0 i) (v1 i) (v2 i) (v3 i))
  refine ⟨a,b,c,d,?_⟩
  dsimp only
  rw [ea, eb, ec, ed]
  intro i
  exact four_slot_inverse (x i) (y i) (v0 i) (v1 i) (v2 i) (v3 i) h4 (hx i) (hy i)

#print axioms natural_eval_surjective
#print axioms natural_four_slot_coverage
end AspisV8R16
