import R1Z.ProverRwP7TraceCloneTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7TraceCloneInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Trace := aspis_statement.state_only_trace.StateOnlyTraceFoundation

def clone (ops : ExternalFuns) (x : Trace) : Result Trace :=
  @ProverRwP7TraceCloneSource.trace_clone _ (ProverRwP6BodyStore.selected ops) x
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterGuardLeaves.selected {ProverRwP6BodyStore.selected ops with op231 := clone ops}

theorem source (ops : ExternalFuns) (x : Trace) :
    (selected ops).op231 x =
      @ProverRwP7TraceCloneSource.trace_clone _ (ProverRwP6BodyStore.selected ops) x := rfl

theorem total (ops : ExternalFuns) (x : Trace) :
    (selected ops).op231 x = ok x :=
  (source ops x).trans (ProverRwP7TraceCloneTotal.source ops x)

theorem callback_removed (ops : ExternalFuns) (callback : Trace → Result Trace) (x : Trace) :
    (selected {ops with op231 := callback}).op231 x = (selected ops).op231 x :=
  (total {ops with op231 := callback} x).trans (total ops x).symm
#print axioms source
#print axioms total
#print axioms callback_removed
end R1Z.ProverRwP7TraceCloneInstall
