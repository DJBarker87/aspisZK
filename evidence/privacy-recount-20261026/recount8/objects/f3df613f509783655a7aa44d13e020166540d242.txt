import R1Z.PV_RW_CompressConcrete
import R1Z.PV_RW_CompressSelectors
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressConcreteBinding
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem emitted_closed (ops : ExternalFuns)
    (out power : aspis_core.field.QM31) (value : U32) (lambda : aspis_core.field.QM31) :
    @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected ops)
      out power value lambda = PV_RW_CompressConcrete.step out power value lambda := by
  unfold PV_RW_CompressEmission.generated.shipped_step
  change (do
    let scaled ← (PV_CurrentScaleInstall.selected ops).op70 power value
    let nextOut ← (PV_CurrentScaleInstall.selected ops).op67 out scaled
    let nextPower ← (PV_CurrentScaleInstall.selected ops).op69 power lambda
    ok (nextOut,nextPower)) = _
  rw [PV_RW_CompressSelectors.scale,PV_RW_CompressSelectors.add,PV_RW_CompressSelectors.mul]
  rfl

theorem independent (left right : ExternalFuns)
    (out power : aspis_core.field.QM31) (value : U32) (lambda : aspis_core.field.QM31) :
    @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected left)
      out power value lambda =
    @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected right)
      out power value lambda := by
  rw [emitted_closed,emitted_closed]

theorem total (ops : ExternalFuns)
    (out power : aspis_core.field.QM31) (value : U32) (lambda : aspis_core.field.QM31) :
    ∃ next, @PV_RW_CompressEmission.generated.shipped_step _ (PV_CurrentScaleInstall.selected ops)
      out power value lambda = ok next := by
  rw [emitted_closed]
  exact PV_RW_CompressConcrete.total out power value lambda
#print axioms emitted_closed
#print axioms independent
#print axioms total
end R1Z.PV_RW_CompressConcreteBinding
