import NDE_PublicBridge
import NDE_ArrayExt
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_PublicExt
open NDE_PublicBridge

theorem option_digest (a b : Option Digest)
    (h : ∀ i : Nat, a.map (fun d => d.val[i]?) = b.map (fun d => d.val[i]?)) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some b => have impossible := h 0; cases impossible
  | some a => cases b with
    | none => have impossible := h 0; cases impossible
    | some b =>
      congr 1
      apply NDE_ArrayExt.words
      intro i
      exact Option.some.inj (h i)

theorem semantic (a b : Semantic)
    (variant : a.variant = b.variant)
    (pool : ∀ i : Nat, a.pool.val[i]? = b.pool.val[i]?)
    (domain : ∀ i : Nat, a.deployment_domain.val[i]? = b.deployment_domain.val[i]?)
    (anchor : ∀ i : Nat, a.anchor.val[i]? = b.anchor.val[i]?)
    (nullifier : ∀ i : Nat, a.nullifier.val[i]? = b.nullifier.val[i]?)
    (asset : a.asset_id = b.asset_id)
    (recipient : ∀ i : Nat, a.recipient.map (fun d => d.val[i]?) = b.recipient.map (fun d => d.val[i]?))
    (change : ∀ i : Nat, a.change.val[i]? = b.change.val[i]?)
    (amount : a.withdrawal_amount = b.withdrawal_amount)
    (transition : a.transition = b.transition) : a = b := by
  have hp := NDE_ArrayExt.words a.pool b.pool pool
  have hd := NDE_ArrayExt.words a.deployment_domain b.deployment_domain domain
  have ha := NDE_ArrayExt.words a.anchor b.anchor anchor
  have hn := NDE_ArrayExt.words a.nullifier b.nullifier nullifier
  have hr := option_digest a.recipient b.recipient recipient
  have hc := NDE_ArrayExt.words a.change b.change change
  cases a; cases b
  simp_all

#print axioms option_digest
#print axioms semantic
end NDE_PublicExt
