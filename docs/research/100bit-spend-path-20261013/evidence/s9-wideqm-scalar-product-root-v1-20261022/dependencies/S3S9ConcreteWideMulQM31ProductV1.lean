import S3S9ConcreteWideMulQM31TotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9ConcreteWideMulQM31ProductV1

abbrev W := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31

/-- Totality and the decoded componentwise product hold for the same result
of the concrete installed helper operation. No successful-operation premise
is exposed: both success and product meaning follow from canonical inputs. -/
theorem concrete_wideMulQM31_total_product (x : W) (q : Q)
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
        ⟨AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM x.c0) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q),
         AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM x.c1) *
          AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9GeneratedWideMulQM31V2.toQM q)⟩ := by
  obtain ⟨z, hz, hcan⟩ :=
    AspisR1S9ConcreteWideMulQM31TotalV1.concrete_wideMulQM31_total x q hx hq
  have hactual :
      AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation x q = .ok z := by
    rw [AspisR1S9ConcreteFieldOpsV1.concrete_wideMulQM31_dispatch] at hz
    exact hz
  have hmeaning :=
    AspisR1S9GeneratedWideMulQM31V2.actualHelperOperation_success
      x q z hx hq hactual
  exact ⟨z, hz, hcan, hmeaning.2⟩

#print axioms concrete_wideMulQM31_total_product

end AspisR1S9ConcreteWideMulQM31ProductV1
