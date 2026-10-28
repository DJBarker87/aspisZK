import R1Z.ProverRw18ContextReference
import R1Z.ProverRw18ContextJoin
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19P6ContextIdentity
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- The owned P6 reference is the previously emitted indexed Rust helper,
-- not a new name for either the original callback or the inline context.
-- Its finite loop is proved in PV_CompressModel.loop. This theorem supplies
-- the context identity for that concrete extraction without a hypothesis.
theorem identity (ops : ExternalFuns) :
    @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops) =
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops) := by
  funext tag values lambda
  exact (@ProverRw18ContextReference.compress _ (PV_CurrentScaleInstall.selected ops)
    tag values lambda).symm

#print axioms identity
end R1Z.ProverRw19P6ContextIdentity
