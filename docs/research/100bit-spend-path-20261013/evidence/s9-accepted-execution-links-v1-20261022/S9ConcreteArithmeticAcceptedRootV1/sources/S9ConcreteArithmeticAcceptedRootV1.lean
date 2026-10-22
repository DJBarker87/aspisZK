import S3S9ConcreteWideMulQM31ScalarProductV1
import S9WideMulM31ReuseRootV2

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S9ConcreteArithmeticAcceptedRootV1
open AspisR1S9HelperP6
abbrev W := field.WideExact
abbrev Q := field.QM31
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev decode := AspisR1S9CurrentFieldOpsV1.decode
abbrev CanonicalQ (q : Q) := AspisR1CurrentWide.Proof.CanonicalQM
  (AspisR1S9GeneratedWideMulQM31V2.toQM q)
abbrev decodeQ (q : Q) := AspisR1CurrentWide.Proof.decodeQM
  (AspisR1S9GeneratedWideMulQM31V2.toQM q)
abbrev ops := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

/-- Reuse constructive totality to identify the exact accepted source product. -/
theorem wideMul_success (x y z : W) (hx : Canonical x) (hy : Canonical y)
    (h : @FieldOps.wideMul ops x y = .ok z) :
    Canonical z ∧ decode z = decode x * decode y := by
  change AspisR1S9ConcreteFieldOpsV1.actualWideMul x y = .ok z at h
  obtain ⟨out, hout, hcan, hdecode⟩ :=
    AspisR1S9ConcreteFieldOpsV1.actualWideMul_total_exact x y hx hy
  have heq : out = z := Result.ok.inj (hout.symm.trans h)
  subst z
  exact ⟨hcan, hdecode⟩

theorem wideAdd_success (x y z : W) (hx : Canonical x) (hy : Canonical y)
    (h : @FieldOps.wideAdd ops x y = .ok z) :
    Canonical z ∧ decode z = decode x + decode y := by
  change AspisR1S9CurrentFieldOpsV1.actualWideAdd x y = .ok z at h
  obtain ⟨out, hout, hcan, hdecode⟩ :=
    AspisR1S9CurrentFieldOpsV1.actualWideAdd_total_exact x y hx hy
  have heq : out = z := Result.ok.inj (hout.symm.trans h)
  subst z
  exact ⟨hcan, hdecode⟩

theorem wideMulM31_success (x z : W) (s : field.M31) (hx : Canonical x)
    (h : @FieldOps.wideMulM31 ops x s = .ok z) :
    Canonical z ∧ decode z = decode x * AspisR1CurrentWide.Proof.wideScalarEmbedding s := by
  exact AspisR1S9CurrentFieldOpsV1.actualWideMulM31_success x z s hx h

theorem wideMulQM31_success (x z : W) (q : Q)
    (hx : Canonical x) (hq : CanonicalQ q)
    (h : @FieldOps.wideMulQM31 ops x q = .ok z) :
    Canonical z ∧ decode z = decode x *
      algebraMap AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact
        (decodeQ q) := by
  obtain ⟨out, hout, hcan, hdecode⟩ :=
    AspisR1S9ConcreteWideMulQM31ScalarProductV1.concrete_wideMulQM31_total_scalar_product
      x q hx hq
  have heq : out = z := Result.ok.inj (hout.symm.trans h)
  subst z
  exact ⟨hcan, hdecode⟩

#print axioms wideMul_success
#print axioms wideAdd_success
#print axioms wideMulM31_success
#print axioms wideMulQM31_success
end AspisR1.S9ConcreteArithmeticAcceptedRootV1
