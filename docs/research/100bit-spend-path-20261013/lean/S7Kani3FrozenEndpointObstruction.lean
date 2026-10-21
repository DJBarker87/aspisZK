import S7Kani2EndpointObstruction
set_option autoImplicit false
namespace AspisR1.S7Kani3FrozenEndpointObstruction
open R1FinalSoundnessBinPerQueryR19
open S7OwnedP6EndpointBoundaryAudit

/-- Even a combined S7/S8/R17 release must first give concrete meanings to
these fields: the requested arbitrary-field restoration is a false target. -/
theorem no_uniform_release_restoration :
    ¬ (∀ s : BoundaryStatements,
      BoundaryEvidence {s with S7 := True,S8 := True,R17 := True} →
      BoundaryEvidence s) := by
  intro restore
  have rest : BoundaryEvidence {falseS7 with S7 := True,S8 := True,R17 := True} := by
    constructor <;> trivial
  exact (restore falseS7 rest).h_S7

#print axioms no_uniform_release_restoration
end AspisR1.S7Kani3FrozenEndpointObstruction
