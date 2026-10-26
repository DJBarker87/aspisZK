import F3M_CircleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleMeaning
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge

def coordinates (p : aspis_core.circle.SecureCirclePoint) : AspisWideTower.WideExact × AspisWideTower.WideExact :=
  (LiteralOpeningView.eK (F3L_RhoMeaning.decode p.x),LiteralOpeningView.eK (F3L_RhoMeaning.decode p.y))

def model (block : Array U8 32#usize) : FinishModel.CircleRow → AspisWideTower.WideExact × AspisWideTower.WideExact
  | .First => (R0P.SemSource.circleSample0 (decodeState block)).1
  | .Second => (R0P.SemSource.circleSample1 (decodeState block)).1

theorem returned (block : Array U8 32#usize) (r : FinishModel.CircleRow)
    (p : aspis_core.circle.SecureCirclePoint) (success : F3M_CircleSource.source block r=ok p) :
    coordinates p=model block r := by
  obtain ⟨actual,call,meaning⟩ :=
    AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.circle_total_coordinates block (F3M_CircleSource.row r)
  have same : F3M_CircleSource.point actual=p := by
    exact Result.ok.inj (by simpa only [F3M_CircleSource.source,call,bind_tc_ok] using success)
  rw [← same]
  have decoded : coordinates (F3M_CircleSource.point actual)=
      AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.coordinates actual :=
    F3M_CircleSource.coordinates actual
  rw [decoded,meaning]
  cases r <;> rfl

#print axioms returned
end AspisR1.F3M_CircleMeaning
end
