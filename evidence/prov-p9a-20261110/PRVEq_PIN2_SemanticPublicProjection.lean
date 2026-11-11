-- PIN2 SemanticPublic projection module (PCXQ_). Source 271869c946d4286db6ee5be784f136599fa8707e, emission PCXQ_E001 Types.lean sha256 ad5c82bdd9b43f2dc1ea78ebb9e354dceb0bca7b71c1c16f530423cca1c17bec
-- (Charon 454586e9 + Aeneas 0d21a9ec). The PIN2 structure below is that emission's SemanticPublic, namespaced as PIN2.SemanticPublic; its field types are the
-- gate's types of AspisR1PublicPreparation (the emitted text of every other type in this module is identical to the gate's: only SemanticPublic changed, one field `destination` added).
import Aeneas
import AspisR1PublicPreparation.Funs
open Aeneas Aeneas.Std
set_option maxHeartbeats 200000
set_option linter.dupNamespace false

namespace PIN2

/-- PIN2 emission of aspis_statement::pool_v1::pair_forest_semantic_terminal::SemanticPublic: the old fields plus `destination`. -/
structure SemanticPublic where
  variant : AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.CompiledVariant
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor : Array AspisR1PublicPreparation.aspis_core.field.M31 8#usize
  nullifier : Array AspisR1PublicPreparation.aspis_core.field.M31 8#usize
  asset_id : AspisR1PublicPreparation.aspis_core.field.M31
  recipient : Option (Array AspisR1PublicPreparation.aspis_core.field.M31 8#usize)
  change : Array AspisR1PublicPreparation.aspis_core.field.M31 8#usize
  withdrawal_amount : Option Std.U32
  destination : Option (Array Std.U8 32#usize)
  transition : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

abbrev OldSP := AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.SemanticPublic

/-- Projection that drops `destination`. -/
def SemanticPublic.dropDestination (x : PIN2.SemanticPublic) : OldSP :=
  { variant := x.variant, pool := x.pool, deployment_domain := x.deployment_domain, anchor := x.anchor,
    nullifier := x.nullifier, asset_id := x.asset_id, recipient := x.recipient, change := x.change,
    withdrawal_amount := x.withdrawal_amount, transition := x.transition }

/-- Embedding that sets `destination := none`. -/
def SemanticPublic.embed (x : OldSP) : PIN2.SemanticPublic :=
  { variant := x.variant, pool := x.pool, deployment_domain := x.deployment_domain, anchor := x.anchor,
    nullifier := x.nullifier, asset_id := x.asset_id, recipient := x.recipient, change := x.change,
    withdrawal_amount := x.withdrawal_amount, destination := none, transition := x.transition }

/-- The PIN2 constructor, projected, is the old constructor on the same nine fields (destination carried but unused). -/
theorem SemanticPublic.dropDestination_mk (v p d a n i r c w dest t) :
    SemanticPublic.dropDestination (PIN2.SemanticPublic.mk v p d a n i r c w dest t)
      = (AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.SemanticPublic.mk v p d a n i r c w t) := rfl

/-- `destination` does not influence the projection. -/
theorem SemanticPublic.dropDestination_set_destination (x : PIN2.SemanticPublic) (d : Option (Array Std.U8 32#usize)) :
    SemanticPublic.dropDestination { x with destination := d } = SemanticPublic.dropDestination x := rfl

theorem SemanticPublic.dropDestination_embed (x : OldSP) :
    SemanticPublic.dropDestination (SemanticPublic.embed x) = x := rfl

theorem SemanticPublic.embed_destination (x : OldSP) : (SemanticPublic.embed x).destination = none := rfl

theorem SemanticPublic.embed_dropDestination (x : PIN2.SemanticPublic) :
    SemanticPublic.embed (SemanticPublic.dropDestination x) = { x with destination := none } := rfl

/-- Two PIN2 values with equal projections and equal destinations are equal. -/
theorem SemanticPublic.eq_of_drop_eq (x y : PIN2.SemanticPublic)
    (h : SemanticPublic.dropDestination x = SemanticPublic.dropDestination y) (hd : x.destination = y.destination) : x = y := by
  cases x; cases y
  simp only [SemanticPublic.dropDestination, OldSP, AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.SemanticPublic.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  simp only at hd
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hd
  rfl

end PIN2

#print axioms PIN2.SemanticPublic.dropDestination_mk
#print axioms PIN2.SemanticPublic.dropDestination_set_destination
#print axioms PIN2.SemanticPublic.dropDestination_embed
#print axioms PIN2.SemanticPublic.embed_destination
#print axioms PIN2.SemanticPublic.embed_dropDestination
#print axioms PIN2.SemanticPublic.eq_of_drop_eq
