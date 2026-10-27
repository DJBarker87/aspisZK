import PoolS2_PolicySource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolS2_PolicyFacts
open Aeneas Aeneas.Std Result PoolS2_PolicySource

def zero : AdapterRw.solana_pubkey.Pubkey := Array.repeat 32#usize 0#u8
def immutable (p : Policy) : Bool := p.flags &&& 1#u8 != 0#u8
def deployment (p : Policy) : Bool := p.flags &&& 2#u8 != 0#u8

def Valid (p : Policy) : Prop :=
  p.flags &&& (~~~ 3#u8) = 0#u8 ∧
  p.registry_program ≠ zero ∧ p.policy_binding ≠ zero ∧
  (deployment p = true → immutable p = true) ∧
  (immutable p = true ↔ p.registry_authority = zero)

theorem accepted (p : Policy)
    (h : pool_v1.format.validate_verifier_policy_v1 p = ok (.Ok ())) : Valid p := by
  classical
  unfold Valid immutable deployment zero
  unfold pool_v1.format.validate_verifier_policy_v1 Hist_Authority.keyEq at h
  repeat' first
  | (solve | cases h)
  | uncase_result
  | head_reduce h
  | split at h
  all_goals first | (solve | aesop) | scalar_tac

#print axioms accepted
end AspisR1.PoolS2_PolicyFacts
end
