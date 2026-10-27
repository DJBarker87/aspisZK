import R1Z.PV_ProverRwP7CoefficientsSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_ProverRwP7CoefficientsInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterGuardLeaves.selected {ProverRwP7FibreInstall.selected ops with
    op255 := @PV_ProverRwP7CoefficientsSource.transport.Variant.coefficients}

theorem source (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (v : transport.Variant) (rows : Array T 1024#usize) :
    (selected ops).op255 copy v rows =
      PV_ProverRwP7CoefficientsSource.transport.Variant.coefficients copy v rows := rfl

theorem callback_removed (ops : ExternalFuns)
    (callback : {T : Type} → core.marker.Copy T → transport.Variant →
      Array T 1024#usize → Result (Array T 1024#usize))
    {T : Type} (copy : core.marker.Copy T) (v : transport.Variant) (rows : Array T 1024#usize) :
    (selected {ops with op255 := @callback}).op255 copy v rows =
      (selected ops).op255 copy v rows := rfl

theorem clone_preserved (ops : ExternalFuns) (x : ProverRwP7TraceCloneInstall.Trace) :
    (selected ops).op231 x = ok x := ProverRwP7TraceCloneInstall.total ops x
theorem fibre_preserved (ops : ExternalFuns) {E : Type}
    (field : aspis_core.r0.scalar.CodeField E) (i : aspis_core.r0.domain.FibreIndex) :
    (selected ops).op78 field i = ProverRwP7FibreSource.fibre field i :=
  ProverRwP7FibreInstall.source ops field i
#print axioms fibre_preserved
#print axioms source
#print axioms callback_removed
#print axioms clone_preserved
end R1Z.PV_ProverRwP7CoefficientsInstall
