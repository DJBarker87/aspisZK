import S3S9ConcreteFieldOpsV1
import S3ScalarFactorTotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConcreteWideMulQM31TotalV1

abbrev Ops := AspisR1S9HelperP6.FieldOps
abbrev W := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31

/-- The concrete installed generated `wideMulQM31` callback is total on the
canonical operands required by the existing source-level component proof. -/
theorem concrete_wideMulQM31_total (x : W) (q : Q)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide x))
    (hq : AspisR1CurrentWide.Proof.CanonicalQM
      (AspisR1S9GeneratedWideMulQM31V2.toQM q)) :
    ∃ z,
      @AspisR1S9HelperP6.FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps x q = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide z) := by
  obtain ⟨z, hz, hcan⟩ :=
    AspisR1S3ScalarFactorTotalV1.actual_helper_mul_total x q hx hq
  exact ⟨z, by rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideMulQM31_dispatch]; exact hz, hcan⟩

#print axioms concrete_wideMulQM31_total

end AspisR1S9ConcreteWideMulQM31TotalV1
