import F3M_CircleSourceCall
import SAP_WrapperCanonical
import SAP_CanonicalCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAP_CircleCanonical
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
attribute [local irreducible] F3M_CircleSource.source AspisR1CircleSampleWrapper.sampler.circle_sample

theorem source (block : Array U8 32#usize) (row : FinishModel.CircleRow)
    (p : aspis_core.circle.SecureCirclePoint) (success : F3M_CircleSource.source block row=ok p) :
    SAP_CanonicalCarrier.CanonK p.x ∧ SAP_CanonicalCarrier.CanonK p.y := by
  obtain ⟨actual,call,_⟩ :=
    AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.circle_total_coordinates block (F3M_CircleSource.row row)
  have same : F3M_CircleSource.point actual=p :=
    Result.ok.inj ((F3M_CircleSourceCall.mapped block row actual call).symm.trans success)
  rw [←same]
  have h := SAP_WrapperCanonical.successful_wrapper_circle_coordinates_canonical
    block (F3M_CircleSource.row row) actual call
  exact h

#print axioms source
end AspisR1.SAP_CircleCanonical
end
