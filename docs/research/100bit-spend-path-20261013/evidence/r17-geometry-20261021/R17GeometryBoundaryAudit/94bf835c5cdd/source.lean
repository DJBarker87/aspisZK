import R1FinalSoundnessHeadline
import R17GeometryClosedForms

/-! A boundary audit, not a replacement soundness endpoint. The opaque
proposition in the actual headline cannot be reconstructed from arithmetic
facts without a stated interpretation connecting that proposition to them. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R17GeometryBoundaryAudit
open R1FinalSoundness FoldFactoredDomain AspisV7ExactOneFoldDomains

def counterexample : BoundaryStatements where
  P1 := True
  P2 := True
  P2_prime := True
  P3 := True
  P4 := True
  P5 := True
  P6 := True
  P7 := True
  R10 := True
  R22 := True
  R4_transport := True
  R17 := False
  R20 := True
  R21 := True
  S1 := True
  S2 := True
  S3 := True
  S4 := True
  S5 := True
  S6 := True
  S7 := True
  S8 := True
  S9 := True
  S10 := True
  M10_uniform := True

/-- Every other actual headline evidence field can hold while R17 is false. -/
theorem other_fields : BoundaryEvidence { counterexample with R17 := True } := by
  constructor <;> trivial

theorem opaque_R17_false : ¬ counterexample.R17 := by
  exact id

/-- Even the proved all-index closed-form table identity does not imply an
arbitrary caller-selected R17 proposition. This is not a geometric mismatch. -/
theorem closed_forms_do_not_fill_opaque_field :
    (∀ u : Fin 262144,
      tableA (u.val &&& 511) * tableB (u.val >>> 9) = storedInitialFibrePoint20 u) ∧
    BoundaryEvidence { counterexample with R17 := True } ∧
    ¬ counterexample.R17 := by
  exact ⟨R17GeometryClosedForms.masked_tables_eq_stored, other_fields, opaque_R17_false⟩

/-- Uniformly restoring the deleted field for arbitrary statements is false. -/
theorem no_uniform_restoration :
    ¬ (∀ s : BoundaryStatements, BoundaryEvidence { s with R17 := True } →
      BoundaryEvidence s) := by
  intro h
  exact opaque_R17_false (h counterexample other_fields).h_R17

#print axioms other_fields
#print axioms opaque_R17_false
#print axioms closed_forms_do_not_fill_opaque_field
#print axioms no_uniform_restoration
end AspisR1.R17GeometryBoundaryAudit
