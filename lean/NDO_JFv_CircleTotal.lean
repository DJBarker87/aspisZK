import RPz7_SAP_CircleCanonical
set_option autoImplicit false
namespace AspisR1.JFv_CircleTotal
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation

theorem source (block : Array U8 32#usize) (row : FinishModel.CircleRow) :
    ∃ point,F3M_CircleSource.source block row=ok point ∧
      SAP_CanonicalCarrier.CanonK point.x ∧ SAP_CanonicalCarrier.CanonK point.y := by
  obtain ⟨actual,call,_⟩ :=
    AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.circle_total_coordinates block (F3M_CircleSource.row row)
  have mapped := F3M_CircleSourceCall.mapped block row actual call
  have canonical := SAP_CircleCanonical.source block row (F3M_CircleSource.point actual) mapped
  exact ⟨F3M_CircleSource.point actual,mapped,canonical⟩

#print axioms source
end AspisR1.JFv_CircleTotal
