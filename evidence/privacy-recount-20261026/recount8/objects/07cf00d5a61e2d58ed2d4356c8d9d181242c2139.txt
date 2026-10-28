import R1Z.PV_Join_AggregateCaller
import R1Z.PV_CB_CandidateDictionary
import R1Z.PV_CB3_Op120Source
import R1Z.PV_CB3_Op51Arbitrary
import R1Z.ProverRwBodyReservationTransport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Selection
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PV_CB_Op229Transport.native
/-- Current exact source selections on the historical P6 aggregate baseline.
This definition changes proof-level callback selection, never shipped code. -/
@[reducible] def installed (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  {PV_CB_CandidateDictionary.selected base (PV_Join_AggregateCaller.selected ops) with
    op51 := @ExternalFuns.op51 _ (PV_CB3_Op51Source.selected ops),
    op120 := @ExternalFuns.op120 _ (PV_CB3_Op120Source.selected ops)}
/-- Preserve the checked reservation/context route after installing source laws. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :=
  @ProverRwOuterGuardLeaves.selected (native base) (installed base ops)
end R1Z.PV_Join_Wire_Selection
