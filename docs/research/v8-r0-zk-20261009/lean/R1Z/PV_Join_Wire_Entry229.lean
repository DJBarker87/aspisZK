import R1Z.PV_Join_Wire_Op229
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Entry229
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op229Transport PV_CB_Op229Source
/-- Source-normal form for exactly this callback, including all Result cases. -/
def source (base : ProverRwFull.ExternalTypes) :
    letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
    aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 →
        aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
        → Result Bool :=
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  fun a b => PV_CB_Op229Source.source (encode base a) (encode base b)
theorem equation (base : ProverRwFull.ExternalTypes)
    (ops : @ProverRwFull.ExternalFuns (PV_Join_Wire_Selection.native base)) :
    @ProverRwFull.ExternalFuns.op229 _ (PV_Join_Wire_Selection.selected base ops) = source base := by
  letI : ProverRwFull.ExternalTypes := PV_Join_Wire_Selection.native base
  funext a b
  exact R1Z.PV_Join_Wire_Op229.op229_source base ops a b
#print axioms equation
end R1Z.PV_Join_Wire_Entry229
