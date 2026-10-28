import R1Z.ProverRwP6BodyData
import R1Z.PV_TraceValueInstall
import R1Z.PV_CB_Op229Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_PublicInstall
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PV_CB_Op229Transport.native
abbrev Late := PV_CB_Op229Transport.Late
/-- Install the exact source operation at the retained native carrier. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  @PV_TraceValueInstall.selected (native base) (PV_CB_Op229Source.selected base ops)

theorem source (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (a b : Late base) :
    @ExternalFuns.op229 (native base) (selected base ops) a b =
      PV_CB_Op229Source.source (PV_CB_Op229Transport.encode base a)
        (PV_CB_Op229Transport.encode base b) :=
  PV_CB_Op229Source.op229_source base ops a b

theorem callback_removed (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (callback : Late base → Late base → Result Bool) :
    letI : ExternalTypes := native base
    selected base {ops with op229 := callback} = selected base ops := by
  letI : ExternalTypes := native base
  have raw : PV_CB_Op229Source.selected base {ops with op229 := callback} =
      PV_CB_Op229Source.selected base ops := rfl
  exact congrArg (@PV_TraceValueInstall.selected (native base)) raw

/-- P6's caller selector retains the newly installed equality verbatim. -/
theorem p6_source (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (a b : Late base) :
    @ExternalFuns.op229 (native base) (@ProverRwP6BodyStore.selected (native base) (selected base ops)) a b =
      PV_CB_Op229Source.source (PV_CB_Op229Transport.encode base a)
        (PV_CB_Op229Transport.encode base b) := source base ops a b
#print axioms source
#print axioms callback_removed
#print axioms p6_source
#print axioms ProverRwP6BodyData.refinement_of_data
end R1Z.PV_Join_PublicInstall
