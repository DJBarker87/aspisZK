import R1Z.PV_CB_CandidateDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_CandidateDictionary
open Aeneas Aeneas.Std Result ProverRwFull
theorem op118 (base : ExternalTypes) (ops : @ExternalFuns (native base)) (x : Array aspis_core.field.QM31 10#usize) :
    (selected base ops).op118 x = (do
      let value ← PV_CB_ShippedOp118.aspis_core.state_only_prefix.r0.statement_points (PV_CB_Op118Transport.encodeArray x)
      ok (PV_CB_Op118Transport.decodePoints value)) := by
  letI : ExternalTypes := native base
  change (PV_CB_Op118Exact.selected ops).op118 x = _
  exact R1Z.PV_CB_Op118Exact.op118_source ops x
#print axioms op118
theorem op229 (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (a b : Late base) :
    (selected base ops).op229 a b = PV_CB_Op229Source.source (PV_CB_Op229Transport.encode base a) (PV_CB_Op229Transport.encode base b) := by
  letI : ExternalTypes := native base
  change (PV_CB_Op229Source.selected base ops).op229 a b = _
  exact R1Z.PV_CB_Op229Source.op229_source base ops a b
#print axioms op229
end R1Z.PV_CB_CandidateDictionary
