import PV_B3P_CompleteTypes227
namespace PV_B3P_Association543227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- The exact fields of inputs16::Public16. No canonicality invariant is added. -/
structure PublicInput543 where
  variant : Bool
  pool : Array U8 32#usize
  domain : Array U8 32#usize
  anchor : Array aspis_core.field.M31 8#usize
  nullifier : Array aspis_core.field.M31 8#usize
  asset : aspis_core.field.M31
  recipient : Option (Array aspis_core.field.M31 8#usize)
  change : Array aspis_core.field.M31 8#usize
  amount : Option U32
  transition : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

def public_from_input543 (p : PublicInput543) : reference_terminal.SemanticPublic :=
  { variant := if p.variant then .Withdrawal else .PrivateTransfer
    pool := p.pool, deployment_domain := p.domain, anchor := p.anchor
    nullifier := p.nullifier, asset_id := p.asset, recipient := p.recipient
    change := p.change, withdrawal_amount := p.amount, transition := p.transition }

def input_from_public543 (p : reference_terminal.SemanticPublic) : PublicInput543 :=
  { variant := match p.variant with | .Withdrawal => true | .PrivateTransfer => false
    pool := p.pool, domain := p.deployment_domain, anchor := p.anchor
    nullifier := p.nullifier, asset := p.asset_id, recipient := p.recipient
    change := p.change, amount := p.withdrawal_amount, transition := p.transition }

theorem public_input_roundtrip543 (p : reference_terminal.SemanticPublic) :
    public_from_input543 (input_from_public543 p) = p := by
  cases p with
  | mk variant pool domain anchor nullifier asset recipient change amount transition =>
    cases variant <;> rfl

theorem input_public_roundtrip543 (p : PublicInput543) :
    input_from_public543 (public_from_input543 p) = p := by
  cases p with
  | mk variant pool domain anchor nullifier asset recipient change amount transition =>
    cases variant <;> rfl

def error_tag543 (e : reference_terminal.PoolV1PairForestSemanticTerminalErrorV1) : U8 :=
  match e with | .InvalidPublicAmount => 0#u8 | .InvalidAppendTransition => 1#u8

theorem error_tag_injective543 : Function.Injective error_tag543 := by
  intro a b h
  cases a <;> cases b <;> simp_all [error_tag543]

#print axioms public_input_roundtrip543
#print axioms input_public_roundtrip543
#print axioms error_tag_injective543
end PV_B3P_Association543227
