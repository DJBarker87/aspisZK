import S3S9ConcreteFieldOpsV1
import S3PowersLowTotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1.S9WideMulM31ReuseRootV2

abbrev W := AspisR1S9HelperP6.field.WideExact
abbrev M := AspisR1S9HelperP6.field.M31
open AspisR1S9CurrentFieldOpsV1

/-- Reuses the existing S3 low-power totality owner for arbitrary raw stored
values, and supplies it to the
same concrete helper slot that the S9 loop executes. -/
theorem concrete_wideMulM31_total (x : W) (s : M) :
    ∃ z, AspisR1S9ConcreteFieldOpsV1.concreteFieldOps.wideMulM31 x s = .ok z := by
  obtain ⟨z, hz⟩ := AspisR1S3PowersLowTotalV1.wide_mul_m31_total (toE x) s
  refine ⟨fromE z, ?_⟩
  change actualWideMulM31 x s = .ok (fromE z)
  simp only [actualWideMulM31, hz, bind_tc_ok]

/-- The previous success-conditional exactness theorem now consumes the
constructed output; successful execution is no longer an antecedent. -/
theorem concrete_wideMulM31_total_exact (x : W) (s : M)
    (hx : Canonical x) :
    ∃ z, AspisR1S9ConcreteFieldOpsV1.concreteFieldOps.wideMulM31 x s = .ok z ∧
      Canonical z ∧ decode z = decode x * AspisR1CurrentWide.Proof.wideScalarEmbedding s := by
  obtain ⟨z, hz⟩ := concrete_wideMulM31_total x s
  refine ⟨z, hz, ?_⟩
  exact actualWideMulM31_success x z s hx hz

#print axioms concrete_wideMulM31_total
#print axioms concrete_wideMulM31_total_exact
end AspisR1.S9WideMulM31ReuseRootV2
