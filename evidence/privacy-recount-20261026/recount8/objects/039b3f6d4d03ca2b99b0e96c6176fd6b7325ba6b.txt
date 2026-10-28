import R1Z.PV_CB_Op229Funs
import R1Z.PV_CB_Op229Codec
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op229Source
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op229Transport
abbrev source := PV_CB_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    @ExternalFuns (native base) :=
  letI : ExternalTypes := native base
  {ops with op229 := fun a b => source (encode base a) (encode base b)}
/-- Exact extracted equality after the proved bijective nominal carrier conversion. -/
theorem op229_source (base : ExternalTypes) (ops : @ExternalFuns (native base))
    (a b : Late base) :
    (selected base ops).op229 a b = source (encode base a) (encode base b) := rfl
#print axioms op229_source
end R1Z.PV_CB_Op229Source
