import R1Z.PV_RunJoin_MergeArray35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_MergeFold35
open PV_RunJoin_FieldData34
abbrev F := AspisR1.ExtractedCurrentQM31Exact.QM31Exact

/-- Independent ordered sample accumulation; each worker index updates its
sample's cell. No source loop, external dictionary or Result is evaluated. -/
def fold : Nat → (Nat → F) → (Nat → F) → Nat → Nat → Nat → F
  | 0,p,_,_,_ => p
  | n+1,p,e,a,i => fold n (Function.update p (i/a) (p (i/a)+e i)) e a (i+1)

theorem map_update (p : Nat → Q) (j : Nat) (q : Q) :
    (fun k => value (Function.update p j q k)) =
      Function.update (fun k => value (p k)) j (value q) := by
  funext k
  by_cases h : k=j
  · subst k;simp only [Function.update_self]
  · simp only [Function.update_of_ne h]

theorem canonical_update (p : Nat → Q) (j : Nat) (q : Q)
    (hp : ∀ k, k<28 → canonical (p k)) (hq : canonical q) :
    ∀ k, k<28 → canonical (Function.update p j q k) := by
  intro k hk
  by_cases h : k=j
  · subst k;simpa only [Function.update_self] using hq
  · simpa only [Function.update_of_ne h] using hp k hk

/-- Prefix splitting keeps exactly the original worker order. -/
theorem split (n m : Nat) (p e : Nat → F) (a i : Nat) :
    fold (n+m) p e a i = fold m (fold n p e a i) e a (i+n) := by
  induction n generalizing p i with
  | zero => simp only [Nat.zero_add,fold,Nat.add_zero]
  | succ n ih =>
    rw [Nat.succ_add,fold,ih,fold]
    congr 1 <;> omega

#print axioms map_update
#print axioms canonical_update
#print axioms split
end R1Z.PV_RunJoin_MergeFold35
