import RPz7_F3M_CircleSourceCall
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleMeaning
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge

def coordinates (p : aspis_core.circle.SecureCirclePoint) : AspisWideTower.WideExact × AspisWideTower.WideExact :=
  (LiteralOpeningView.eK (F3L_RhoMeaning.decode p.x),LiteralOpeningView.eK (F3L_RhoMeaning.decode p.y))

attribute [local irreducible] F3M_CircleSource.source AspisR1CircleSampleWrapper.sampler.circle_sample

theorem returned (block : Array U8 32#usize) (r : FinishModel.CircleRow)
    (p : aspis_core.circle.SecureCirclePoint) (success : F3M_CircleSource.source block r=ok p) :
    coordinates p=(AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.model block (F3M_CircleSource.row r)).1 := by
  obtain ⟨actual,call,meaning⟩ :=
    AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.circle_total_coordinates block (F3M_CircleSource.row r)
  have same : F3M_CircleSource.point actual=p :=
    Result.ok.inj ((F3M_CircleSourceCall.mapped block r actual call).symm.trans success)
  exact (congrArg coordinates same).symm.trans
    ((F3M_CircleSource.coordinates actual).trans meaning)

#print axioms returned
end AspisR1.F3M_CircleMeaning
end
