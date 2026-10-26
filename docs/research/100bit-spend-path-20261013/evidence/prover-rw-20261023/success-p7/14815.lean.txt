import R1Z.ProverRwP7FibreSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP7FibreInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterGuardLeaves.selected {ProverRwP7TraceCloneInstall.selected ops with
    op78 := @ProverRwP7FibreSource.fibre}

theorem source (ops : ExternalFuns) {E : Type} (field : aspis_core.r0.scalar.CodeField E)
    (i : aspis_core.r0.domain.FibreIndex) :
    (selected ops).op78 field i = ProverRwP7FibreSource.fibre field i := rfl

theorem callback_removed (ops : ExternalFuns)
    (callback : {E : Type} → aspis_core.r0.scalar.CodeField E →
      aspis_core.r0.domain.FibreIndex → Result (aspis_core.r0.domain.Point E))
    {E : Type} (field : aspis_core.r0.scalar.CodeField E)
    (i : aspis_core.r0.domain.FibreIndex) :
    (selected {ops with op78 := @callback}).op78 field i = (selected ops).op78 field i := rfl

theorem clone_preserved (ops : ExternalFuns) (x : ProverRwP7TraceCloneInstall.Trace) :
    (selected ops).op231 x = ok x := ProverRwP7TraceCloneInstall.total ops x
#print axioms source
#print axioms callback_removed
#print axioms clone_preserved
end R1Z.ProverRwP7FibreInstall
