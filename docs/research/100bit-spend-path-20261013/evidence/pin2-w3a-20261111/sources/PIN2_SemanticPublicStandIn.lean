-- TEMPORARY stand-in (PIN2 W3a, 2026-11-11): replace by Stream C's PIN2 emission.
-- Stream C's PRVEq_PIN2_SemanticPublicProjection covers only the
-- AspisR1PublicPreparation crate. The builders of group (b) read the
-- aspis_r1_mask_extraction_probe native crate (`FIq_Native`, RPu_FIq_NativeTypes),
-- for which no PIN2 emission exists yet. This module mirrors that crate's
-- extracted SemanticPublic plus `destination : Option (Array U8 32#usize)`, with
-- the same field order, names and projection API as PRVEq_PIN2_SemanticPublicProjection,
-- so the swap is one import line plus one namespace. It is handwritten, not extracted.
import RPu_FIq_NativeTypes
open Aeneas Aeneas.Std
set_option autoImplicit false

namespace PIN2Native

open FIq_Native in
/-- Stand-in for the PIN2 emission of the native crate's SemanticPublic
(replace by Stream C's PIN2 emission). -/
structure SemanticPublic where
  variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor : Array field.M31 8#usize
  nullifier : Array field.M31 8#usize
  asset_id : field.M31
  recipient : Option (Array field.M31 8#usize)
  change : Array field.M31 8#usize
  withdrawal_amount : Option Std.U32
  destination : Option (Array Std.U8 32#usize)
  transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

abbrev OldSP := FIq_Native.pool_v1.pair_forest_semantic_terminal.SemanticPublic

/-- Projection that drops `destination`. -/
def SemanticPublic.dropDestination (x : SemanticPublic) : OldSP :=
  { variant := x.variant, pool := x.pool, deployment_domain := x.deployment_domain, anchor := x.anchor,
    nullifier := x.nullifier, asset_id := x.asset_id, recipient := x.recipient, change := x.change,
    withdrawal_amount := x.withdrawal_amount, transition := x.transition }

/-- Embedding that sets `destination := none`. -/
def SemanticPublic.embed (x : OldSP) : SemanticPublic :=
  { variant := x.variant, pool := x.pool, deployment_domain := x.deployment_domain, anchor := x.anchor,
    nullifier := x.nullifier, asset_id := x.asset_id, recipient := x.recipient, change := x.change,
    withdrawal_amount := x.withdrawal_amount, destination := none, transition := x.transition }

theorem SemanticPublic.dropDestination_embed (x : OldSP) :
    SemanticPublic.dropDestination (SemanticPublic.embed x) = x := rfl

theorem SemanticPublic.embed_destination (x : OldSP) : (SemanticPublic.embed x).destination = none := rfl

theorem SemanticPublic.dropDestination_set_destination (x : SemanticPublic)
    (d : Option (Array Std.U8 32#usize)) :
    SemanticPublic.dropDestination { x with destination := d } = SemanticPublic.dropDestination x := rfl

/-- One source byte as a model byte (`Fin 256`); exact, since `b.val < 256`. -/
def byte (b : Std.U8) : Fin 256 := ⟨b.val % 256, Nat.mod_lt _ (by decide)⟩

/-- A source `[u8; 32]` as the model's byte list. -/
def bytes32 (a : Array Std.U8 32#usize) : List (Fin 256) := a.val.map byte

theorem bytes32_length (a : Array Std.U8 32#usize) : (bytes32 a).length = 32 := by
  simp [bytes32, a.property]

/-- Field projections of the pre-PIN2 view are the PIN2 fields. -/
@[simp] theorem SemanticPublic.dropDestination_variant (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).variant = x.variant := rfl
@[simp] theorem SemanticPublic.dropDestination_pool (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).pool = x.pool := rfl
@[simp] theorem SemanticPublic.dropDestination_deployment_domain (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).deployment_domain = x.deployment_domain := rfl
@[simp] theorem SemanticPublic.dropDestination_anchor (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).anchor = x.anchor := rfl
@[simp] theorem SemanticPublic.dropDestination_nullifier (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).nullifier = x.nullifier := rfl
@[simp] theorem SemanticPublic.dropDestination_asset_id (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).asset_id = x.asset_id := rfl
@[simp] theorem SemanticPublic.dropDestination_recipient (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).recipient = x.recipient := rfl
@[simp] theorem SemanticPublic.dropDestination_change (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).change = x.change := rfl
@[simp] theorem SemanticPublic.dropDestination_withdrawal_amount (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).withdrawal_amount = x.withdrawal_amount := rfl
@[simp] theorem SemanticPublic.dropDestination_transition (x : SemanticPublic) :
    (SemanticPublic.dropDestination x).transition = x.transition := rfl

end PIN2Native

/-- Rewrite every pre-PIN2 field projection of `dropDestination p` to `p`'s field
(replace by Stream C's PIN2 emission together with this module). -/
syntax "pin2_drop" : tactic
macro_rules
  | `(tactic| pin2_drop) => `(tactic| try simp only [PIN2Native.SemanticPublic.dropDestination_variant, PIN2Native.SemanticPublic.dropDestination_pool, PIN2Native.SemanticPublic.dropDestination_deployment_domain, PIN2Native.SemanticPublic.dropDestination_anchor, PIN2Native.SemanticPublic.dropDestination_nullifier, PIN2Native.SemanticPublic.dropDestination_asset_id, PIN2Native.SemanticPublic.dropDestination_recipient, PIN2Native.SemanticPublic.dropDestination_change, PIN2Native.SemanticPublic.dropDestination_withdrawal_amount, PIN2Native.SemanticPublic.dropDestination_transition] at *)

#print axioms PIN2Native.SemanticPublic.dropDestination_embed
#print axioms PIN2Native.bytes32_length
