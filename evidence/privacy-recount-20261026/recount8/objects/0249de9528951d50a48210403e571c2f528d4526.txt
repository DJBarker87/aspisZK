import R1Z.ProverRw19P6ContextIdentity
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19P6Join
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- P_source_p6 is still OPEN. Neither this consumer nor the P6 reference
-- proves that the original op223 has the reference's semantics.
-- Unlike rw18.callback, there is no arbitrary extracted function and no
-- context_identity premise: the concrete reference identity is supplied.
theorem callback (ops : ExternalFuns)
    (P_source_p6 : ops.op223 =
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)) :
    ops.op223 = PV_RW_CompressClosed.owned :=
  ProverRw18ContextJoin.callback ops _ P_source_p6
    (ProverRw19P6ContextIdentity.identity ops)

theorem dictionaries (ops : ExternalFuns)
    (P_source_p6 : ops.op223 =
      @ProverRwP6CompressSource.compress _ (PV_CurrentScaleInstall.selected ops)) :
    ProverRw18ContextJoin.original ops = ProverRw18ContextJoin.owned ops :=
  ProverRw18ContextJoin.dictionaries ops _ P_source_p6
    (ProverRw19P6ContextIdentity.identity ops)

#print axioms callback
#print axioms dictionaries
end R1Z.ProverRw19P6Join
