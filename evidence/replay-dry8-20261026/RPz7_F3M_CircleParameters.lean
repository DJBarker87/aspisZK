import RPz7_F3M_CircleFirstModel
import RPz7_F3M_CircleSecondModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleParameters
open AspisV8R19.SourceDuplexStep
attribute [local irreducible] R0P.SemSource.circleSampleParameter0 R0P.SemSource.circleSampleParameter1

theorem first (state : State) :
    R0P.SemSource.circleSample0 state=
      R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf (SelectedChallengeMap.sigma 25 state)) := by
  have sigma : SelectedChallengeMap.sigma 25 state=R0P.SemSource.semChal state := by
    simp only [SelectedChallengeMap.sigma,show (25 : Nat)≠27 by decide,
      show ¬((25 : Nat)=28 ∨ 25=29 ∨ 25=30) by decide,show (25 : Nat)≠31 by decide,if_false]
  rw [sigma,SelectedChallengeMap.semChal_re]
  rfl

theorem second (state : State) :
    R0P.SemSource.circleSample1 state=
      R0P.SemSource.circleSampleParameter1 (SelectedChallengeMap.rhoOf (SelectedChallengeMap.sigma 26 state)) := by
  have sigma : SelectedChallengeMap.sigma 26 state=R0P.SemSource.semChal state := by
    simp only [SelectedChallengeMap.sigma,show (26 : Nat)≠27 by decide,
      show ¬((26 : Nat)=28 ∨ 26=29 ∨ 26=30) by decide,show (26 : Nat)≠31 by decide,if_false]
  rw [sigma,SelectedChallengeMap.semChal_re]
  rfl

#print axioms first
#print axioms second
end AspisR1.F3M_CircleParameters
end
