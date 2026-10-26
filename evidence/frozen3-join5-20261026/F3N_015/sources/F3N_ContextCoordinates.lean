import F3M_OpeningReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_ContextCoordinates

def four {K : Type*} (x0 y0 x1 y1 : K) : Fin 4 → K := fun j=>
  if j.val=0 then x0 else if j.val=1 then y0 else if j.val=2 then x1 else y1

theorem context (v : LiteralOpeningView.View)
    (p0 p1 : AspisR0.ChordGeometry.Point AspisWideTower.WideExact)
    (shape : v.circlePoints=(fun j=>if j.val=0 then p0 else p1)) :
    OraclePortAcceptedContextC6.coordinates v=four
      (SelectedChallengeMap.rhoOf p0.1.1) (SelectedChallengeMap.rhoOf p0.1.2)
      (SelectedChallengeMap.rhoOf p1.1.1) (SelectedChallengeMap.rhoOf p1.1.2) := by
  unfold OraclePortAcceptedContextC6.coordinates four
  rw [shape]
  rfl

#print axioms context
end AspisR1.F3N_ContextCoordinates
end
