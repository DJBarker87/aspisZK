import F3M_CircleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleModel
open Aeneas Aeneas.Std AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge

def model (block : Array U8 32#usize) : FinishModel.CircleRow → AspisWideTower.WideExact × AspisWideTower.WideExact
  | .First => (R0P.SemSource.circleSample0 (decodeState block)).1
  | .Second => (R0P.SemSource.circleSample1 (decodeState block)).1

theorem row (block : Array U8 32#usize) (r : FinishModel.CircleRow) :
    (AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.model block (F3M_CircleSource.row r)).1=
      model block r := by
  cases r <;> rfl

#print axioms row
end AspisR1.F3M_CircleModel
end
