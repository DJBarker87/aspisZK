import S3S9ConcreteWideMulQM31ProductV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConcreteWideMulQM31ScalarProductV1

abbrev W := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev ExactQM := AspisR1S9HelperP6PowerSemanticsV1.ExactQM
abbrev ExactWide := AspisWideTower.WideExact

private theorem componentwise_mul_is_algebraMap (a b q : ExactQM) :
    (⟨a * q, b * q⟩ : ExactWide) =
      (⟨a,b⟩ : ExactWide) * algebraMap ExactQM ExactWide q := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im, zero_mul, mul_zero, add_zero]
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im, zero_mul, mul_zero, zero_add, add_zero]

/-- The concrete mixed multiplication result is scalar multiplication by the
QM31 embedding in the exact quadratic extension. Success and canonicality
remain derived from the same canonical-input result. -/
theorem concrete_wideMulQM31_total_scalar_product (x : W) (q : Q)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x))
    (hq : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q)) :
    ∃ z,
      @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x q = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide z) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide z) =
        AspisR1CurrentWide.Proof.decodeWide
          (AspisR1S9GeneratedWideMulQM31V2.toWide x) *
        algebraMap ExactQM ExactWide
          (AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q)) := by
  obtain ⟨z,hz,hcan,hprod⟩ :=
    AspisR1S9ConcreteWideMulQM31ProductV1.concrete_wideMulQM31_total_product
      x q hx hq
  refine ⟨z,hz,hcan,?_⟩
  rw [hprod]
  simpa only [AspisR1CurrentWide.Proof.decodeWide,
      AspisR1S9GeneratedWideMulQM31V2.toWide] using
    componentwise_mul_is_algebraMap
      (AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x.c0))
      (AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM x.c1))
      (AspisR1CurrentWide.Proof.decodeQM
        (AspisR1S9GeneratedWideMulQM31V2.toQM q))

#print axioms concrete_wideMulQM31_total_scalar_product

end AspisR1S9ConcreteWideMulQM31ScalarProductV1
