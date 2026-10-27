import R1Z.PV_Join_PublicInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_PublicDictionary
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PV_Join_PublicInstall.native
abbrev Late := PV_Join_PublicInstall.Late
def raw (base : ExternalTypes) (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) := by
  letI : ExternalTypes := native base
  exact {ops with op229 := fun a b =>
    PV_CB_Op229Source.source (PV_CB_Op229Transport.encode base a) (PV_CB_Op229Transport.encode base b)}

theorem raw_form (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    PV_CB_Op229Source.selected base ops = raw base ops := by
  letI : ExternalTypes := native base
  have law : (PV_CB_Op229Source.selected base ops).op229 =
      (fun a b => PV_CB_Op229Source.source (PV_CB_Op229Transport.encode base a)
        (PV_CB_Op229Transport.encode base b)) := by
    funext a b
    exact PV_CB_Op229Source.op229_source base ops a b
  change {ops with op229 := (PV_CB_Op229Source.selected base ops).op229} = raw base ops
  rw [law]
  rfl

theorem dictionary (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    PV_Join_PublicInstall.selected base ops =
      @PV_TraceValueInstall.selected (native base) (raw base ops) := by
  unfold PV_Join_PublicInstall.selected
  rw [raw_form]
#print axioms raw_form
#print axioms dictionary
end R1Z.PV_Join_PublicDictionary
