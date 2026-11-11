-- PIN2 W3c (2026-11-11): helpers over Stream C's probe-crate PIN2 emission
-- (PRVEq_PIN2_ProbeSemanticPublicProjection, source sha 514a39a68d01..., imported here
-- through PIN2P_ProbeProjectionRPu, which differs only in naming the closure's module
-- RPu_FIq_NativeTypes for the same gate file).  This replaces W3a's
-- PIN2_SemanticPublicStandIn: the SemanticPublic structure, dropDestination and embed now
-- come from the emission; only the byte helpers, the per-field projection simp lemmas
-- (all `rfl` on the emitted dropDestination) and the `pin2_drop` tactic remain here.
-- Provenance of the struct: probe crate aspis_r1_mask_extraction_probe (HM-D at best).
import PIN2P_ProbeProjectionRPu
open Aeneas Aeneas.Std
set_option autoImplicit false

namespace PIN2P

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

end PIN2P

/-- Rewrite every pre-PIN2 field projection of `dropDestination p` to `p`'s field
(helpers over the probe-crate PIN2 emission; not extracted). -/
syntax "pin2_drop" : tactic
macro_rules
  | `(tactic| pin2_drop) => `(tactic| try simp only [PIN2P.SemanticPublic.dropDestination_variant, PIN2P.SemanticPublic.dropDestination_pool, PIN2P.SemanticPublic.dropDestination_deployment_domain, PIN2P.SemanticPublic.dropDestination_anchor, PIN2P.SemanticPublic.dropDestination_nullifier, PIN2P.SemanticPublic.dropDestination_asset_id, PIN2P.SemanticPublic.dropDestination_recipient, PIN2P.SemanticPublic.dropDestination_change, PIN2P.SemanticPublic.dropDestination_withdrawal_amount, PIN2P.SemanticPublic.dropDestination_transition] at *)

#print axioms PIN2P.bytes32_length
