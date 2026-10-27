import R1Z.ProverRw21Arity16Endpoint
import R1Z.ProverRw19P6ContextIdentity
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21Arity16Reference
open Aeneas Aeneas.Std Result ProverRwFull ProverRw21Arity16Endpoint
variable [ExternalTypes]

/-- The native source binding is still an obligation, here restricted to the
only array shape emitted by the caller. This does not discharge P_source_p6. -/
def Source16 (ops : ExternalFuns) : Prop := Agree16 ops.op223
  (@ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops))

theorem reference (ops : ExternalFuns) :
    @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)=PV_RW_CompressClosed.owned := by
  rw [ProverRw19P6ContextIdentity.identity ops]
  funext tag values lambda
  exact ProverRw18ContextCompression.owned ops tag values lambda

theorem restricted (ops : ExternalFuns)
    (source : ops.op223=@ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)) :
    Source16 ops := by
  intro tag values lambda
  rw [source]

theorem owned (ops : ExternalFuns) (source : Source16 ops) :
    Agree16 ops.op223 PV_RW_CompressClosed.owned := by
  unfold Source16 at source
  rw [reference ops] at source
  exact source

#print axioms Source16
#print axioms reference
#print axioms restricted
#print axioms owned
end R1Z.ProverRw21Arity16Reference
