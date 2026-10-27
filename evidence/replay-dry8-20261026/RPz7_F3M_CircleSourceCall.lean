import RPz7_F3M_CircleSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleSourceCall
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
attribute [local irreducible] AspisR1CircleSampleWrapper.sampler.circle_sample

theorem mapped (block : Array U8 32#usize) (r : FinishModel.CircleRow)
    (actual : AspisR1CircleSampleWrapper.circle.SecureCirclePoint)
    (call : AspisR1CircleSampleWrapper.sampler.circle_sample block (F3M_CircleSource.row r)=ok actual) :
    F3M_CircleSource.source block r=ok (F3M_CircleSource.point actual) := by
  unfold F3M_CircleSource.source
  rw [call]
  rfl

#print axioms mapped
end AspisR1.F3M_CircleSourceCall
end
