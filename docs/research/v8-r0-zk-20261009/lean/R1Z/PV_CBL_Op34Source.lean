import R1Z.PV_CBL_Op34Transport
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_Op34Source
open ProverRwFull
set_option autoImplicit false
variable [ExternalTypes]

/-- Selection of the safe owned length-test reference. Native gate and
extraction provenance are recorded separately; this does not assert RunJoin. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { ops with op34 := fun {T} _ v => PV_CBL_Op34Reference.empty_reference (T := T) v }

theorem op34_source (ops : ExternalFuns) {T : Type} (A : Type)
    (v : alloc.vec.Vec T) :
    (selected ops).op34 A v = PV_CBL_Op34Reference.empty_reference v := rfl
#print axioms op34_source
end R1Z.PV_CBL_Op34Source
