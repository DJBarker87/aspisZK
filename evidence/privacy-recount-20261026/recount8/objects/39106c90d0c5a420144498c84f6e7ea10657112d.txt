import R1Z.PV_RW_CompressIterator
import R1Z.PV_CurrentScaleInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_CompressDictionaries
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- Auxiliary source-model dictionaries, not a live callback installation.
-- Native association of the iterator source model remains a separate gate.
@[reducible] def source (ops : ExternalFuns) : ExternalFuns :=
  let base := PV_CurrentScaleInstall.selected ops
  {base with op223 := @PV_RW_CompressIterator.compress _ base}
@[reducible] def reference (ops : ExternalFuns) : ExternalFuns :=
  let base := PV_CurrentScaleInstall.selected ops
  {base with op223 := @ProverRwP6CompressSource.compress _ base}

theorem equal (ops : ExternalFuns) : source ops = reference ops := by
  have same : @PV_RW_CompressIterator.compress _ (PV_CurrentScaleInstall.selected ops) =
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops) := by
    funext tag values lambda
    exact @PV_RW_CompressIterator.reference _ (PV_CurrentScaleInstall.selected ops) tag values lambda
  dsimp only [source,reference]
  rw [same]

#print axioms equal
end R1Z.PV_RW_CompressDictionaries
