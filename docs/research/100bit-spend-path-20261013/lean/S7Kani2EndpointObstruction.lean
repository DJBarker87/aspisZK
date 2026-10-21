import S7OwnedP6EndpointBoundaryAudit

/-! The requested deletion-only endpoint operation is false for arbitrary
BoundaryStatements, even if every other field is true. Concrete production
refinements must first be interpreted in that interface. -/
set_option autoImplicit false
namespace AspisR1.S7Kani2EndpointObstruction
open R1FinalSoundnessBinPerQueryR19
open S7OwnedP6EndpointBoundaryAudit

def falseR17 : BoundaryStatements := {falseS7 with S7 := True,R17 := False}

theorem other_r17_fields : BoundaryEvidence {falseR17 with R17 := True} := by
  constructor <;> trivial

theorem no_uniform_r17_restoration :
    ¬ (∀ s : BoundaryStatements, BoundaryEvidence {s with R17 := True} →
      BoundaryEvidence s) := by
  intro restore
  exact (restore falseR17 other_r17_fields).h_R17

theorem no_uniform_joint_restoration :
    ¬ (∀ s : BoundaryStatements, BoundaryEvidence {s with S7 := True,R17 := True} →
      BoundaryEvidence s) := by
  intro restore
  have rest : BoundaryEvidence {falseS7 with S7 := True,R17 := True} := by
    constructor <;> trivial
  exact (restore falseS7 rest).h_S7

#print axioms other_r17_fields
#print axioms no_uniform_r17_restoration
#print axioms no_uniform_joint_restoration
end AspisR1.S7Kani2EndpointObstruction
