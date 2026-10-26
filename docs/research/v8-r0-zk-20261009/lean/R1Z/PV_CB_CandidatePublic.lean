import R1Z.PV_CB_CandidateDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
theorem op229 (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (a b : Late base) :
    (selected base ops).op229 a b = PV_CB_Op229Source.source (PV_CB_Op229Transport.encode base a) (PV_CB_Op229Transport.encode base b) := by
  change (PV_CB_Op229Source.selected base ops).op229 a b = _
  exact R1Z.PV_CB_Op229Source.op229_source base ops a b
#print axioms op229
end R1Z.PV_CB_CandidateDictionary
