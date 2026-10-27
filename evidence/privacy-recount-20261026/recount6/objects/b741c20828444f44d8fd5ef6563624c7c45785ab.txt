import R1Z.PV_Join_PublicInstall
import R1Z.PV_CB3_Op229Source
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_PublicCarrierBridge
open Aeneas Aeneas.Std Result ProverRwFull
abbrev native := PV_Join_PublicInstall.native
abbrev Late := PV_Join_PublicInstall.Late
abbrev CB3Late (base : ExternalTypes) :=
  @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
    (PV_CB3_Afterstate.selectedTypes base)
def encode (base : ExternalTypes) (x : Late base) : CB3Late base := by
  letI : ExternalTypes := native base
  exact @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.mk
    (PV_CB3_Afterstate.selectedTypes base) x.live_snapshot ⟨x.candidate_afterstate.next_pair_index,
    x.candidate_afterstate.next_root,x.candidate_afterstate.next_frontier⟩
def decode (base : ExternalTypes) (x : CB3Late base) : Late base := by
  letI : ExternalTypes := PV_CB3_Afterstate.selectedTypes base
  exact @aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.mk
    (native base) x.live_snapshot (PV_CB_Op229Transport.unafter ⟨x.candidate_afterstate.next_pair_index,
    x.candidate_afterstate.next_root,x.candidate_afterstate.next_frontier⟩)
theorem roundtrip (base : ExternalTypes) (x : Late base) : decode base (encode base x) = x := by
  cases x with
  | mk live after => cases after; rfl
theorem source_roundtrip (base : ExternalTypes) (x : CB3Late base) : encode base (decode base x) = x := by
  cases x with
  | mk live after => cases after; rfl
/-- Both independently extracted equations preserve the entire Bool Result. -/
theorem source (base : ExternalTypes) (a b : Late base) :
    PV_CB_Op229Source.source (PV_CB_Op229Transport.encode base a)
      (PV_CB_Op229Transport.encode base b) =
    PV_CB3_ShippedOp229.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq
      (encode base a) (encode base b) := by
  rfl
#print axioms roundtrip
#print axioms source_roundtrip
#print axioms source
end R1Z.PV_Join_PublicCarrierBridge
