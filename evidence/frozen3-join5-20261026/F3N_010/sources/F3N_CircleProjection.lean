import F3N_CircleCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_CircleProjection
open AspisR1PublicPreparation
attribute [local irreducible] F3L_RhoMeaning.decode R0P.SemSource.circleSampleParameter0
  R0P.SemSource.circleSampleParameter1

theorem pair (p : aspis_core.circle.SecureCirclePoint)
    (q : AspisWideTower.WideExact × AspisWideTower.WideExact)
    (same : F3M_CircleMeaning.coordinates p=q) :
    F3L_RhoMeaning.decode p.x=SelectedChallengeMap.rhoOf q.1 ∧
    F3L_RhoMeaning.decode p.y=SelectedChallengeMap.rhoOf q.2 := by
  constructor
  · exact congrArg (fun z=>SelectedChallengeMap.rhoOf z.1) same
  · exact congrArg (fun z=>SelectedChallengeMap.rhoOf z.2) same

#print axioms pair
end AspisR1.F3N_CircleProjection
end
