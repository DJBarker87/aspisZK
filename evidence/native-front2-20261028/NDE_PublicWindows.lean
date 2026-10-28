import NDE_PublicExt
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_PublicWindows
open NDE_PublicBridge

theorem recipient (a b : Option Digest)
    (h : ∀ i : Nat, i < 8 → a.map (fun d => d.val[i]?) = b.map (fun d => d.val[i]?)) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some b => have impossible := h 0 (by decide); cases impossible
  | some a => cases b with
    | none => have impossible := h 0 (by decide); cases impossible
    | some b =>
      congr 1
      apply NDE_ArrayExt.bounded_words
      intro i hi
      exact Option.some.inj (h i hi)

theorem semantic (a b : Semantic)
    (variant : a.variant = b.variant)
    (pool : ∀ i : Nat, i < 32 → a.pool.val[i]? = b.pool.val[i]?)
    (domain : ∀ i : Nat, i < 32 → a.deployment_domain.val[i]? = b.deployment_domain.val[i]?)
    (anchor : ∀ i : Nat, i < 8 → a.anchor.val[i]? = b.anchor.val[i]?)
    (nullifier : ∀ i : Nat, i < 8 → a.nullifier.val[i]? = b.nullifier.val[i]?)
    (asset : a.asset_id = b.asset_id)
    (recipientWords : ∀ i : Nat, i < 8 → a.recipient.map (fun d => d.val[i]?) = b.recipient.map (fun d => d.val[i]?))
    (change : ∀ i : Nat, i < 8 → a.change.val[i]? = b.change.val[i]?)
    (amount : a.withdrawal_amount = b.withdrawal_amount)
    (transition : a.transition = b.transition) : a = b := by
  have hp := NDE_ArrayExt.bounded_words a.pool b.pool pool
  have hd := NDE_ArrayExt.bounded_words a.deployment_domain b.deployment_domain domain
  have ha := NDE_ArrayExt.bounded_words a.anchor b.anchor anchor
  have hn := NDE_ArrayExt.bounded_words a.nullifier b.nullifier nullifier
  have hr := recipient a.recipient b.recipient recipientWords
  have hc := NDE_ArrayExt.bounded_words a.change b.change change
  cases a; cases b
  simp_all

#print axioms recipient
#print axioms semantic
end NDE_PublicWindows
