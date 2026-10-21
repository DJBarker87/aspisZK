import R1FinalSoundnessBinPerQueryR19

/-! Audit of the actual requested endpoint's opaque S7 field. This does not
refute a concrete source relation or prevent a newly interpreted endpoint. -/
set_option autoImplicit false
namespace AspisR1.S7OwnedP6EndpointBoundaryAudit
open R1FinalSoundnessBinPerQueryR19
def falseS7 : BoundaryStatements where
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
  R17 := True
  R20 := True
  R21 := True
  S1 := True
  S2 := True
  S3 := True
  S4 := True
  S5 := True
  S6 := True
  S7 := False
  S8 := True
  S9 := True
  S10 := True
  M10_uniform := True


theorem all_other_boundaries : BoundaryEvidence { falseS7 with S7 := True } := by
  constructor <;> trivial

/-- Filling arbitrary S7 from the remaining fields is a false target,
independently of how much concrete arithmetic correspondence is proved. -/
theorem no_uniform_s7_restoration :
    ¬ (∀ s : BoundaryStatements, BoundaryEvidence { s with S7 := True } →
      BoundaryEvidence s) := by
  intro restore
  exact (restore falseS7 all_other_boundaries).h_S7

#print axioms all_other_boundaries
#print axioms no_uniform_s7_restoration
end AspisR1.S7OwnedP6EndpointBoundaryAudit
