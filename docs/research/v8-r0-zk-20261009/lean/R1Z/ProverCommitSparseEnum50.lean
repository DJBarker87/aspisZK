import R1Z.ProverCommitSparseConcat50
import R1Z.ProverCommitSparse50
/-! Exact prefix/suffix row enumeration and dense-to-sparse equality.
All dimensions and field values remain symbolic. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSparseEnum50
open ProverCommitBooleanEnum49 ProverCommitSparseConcat50
open scoped BigOperators

theorem injective (m n : Nat) : Function.Injective (fun ab : Fin (2^m) × Fin (2^n) => concat m n ab.1 ab.2) := by
  intro a b h
  apply Prod.ext
  · apply ProverCommitBooleanEnum49.injective m
    funext i
    have hh := congrArg (fun r => tail (m+n) r (i.castAdd n)) h
    simpa only [high] using hh
  · apply ProverCommitBooleanEnum49.injective n
    funext i
    have hh := congrArg (fun r => tail (m+n) r (i.natAdd m)) h
    simpa only [low] using hh

theorem bijective (m n : Nat) : Function.Bijective (fun ab : Fin (2^m) × Fin (2^n) => concat m n ab.1 ab.2) := by
  refine ⟨injective m n,?_⟩
  by_contra hn
  have hc := Fintype.card_lt_of_injective_not_surjective _ (injective m n) hn
  simp only [Fintype.card_prod,Fintype.card_fin,←pow_add] at hc
  exact (Nat.lt_irrefl _) hc

def equiv (m n : Nat) : Fin (2^m) × Fin (2^n) ≃ Fin (2^(m+n)) :=
  Equiv.ofBijective _ (bijective m n)

theorem sum_concat {K : Type} [AddCommMonoid K] (m n : Nat) (f : Fin (2^(m+n)) → K) :
    (∑ r, f r)=∑ a : Fin (2^m), ∑ b : Fin (2^n), f (concat m n a b) := by
  rw [←Equiv.sum_comp (equiv m n) f,Fintype.sum_prod_type]
  rfl

theorem append_weight {K : Type} [Field K] (m n : Nat)
    (p : Fin m → K) (q : Fin n → K) (a : Fin m → Bool) (b : Fin n → Bool) :
    ProverCommitSparse50.weight (Fin.append p q) (Fin.append a b)=
      ProverCommitSparse50.weight p a*ProverCommitSparse50.weight q b := by
  simp only [ProverCommitSparse50.weight,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

theorem prune {K : Type} [Field K] (m n : Nat) (p : Fin m → K)
    (suffix : Fin (2^n)) (f : Fin (2^(m+n)) → K) :
    (∑ r, ProverCommitSparse50.weight
      (Fin.append p (fun i => if tail n suffix i then (1:K) else 0)) (tail (m+n) r)*f r)=
      ∑ a : Fin (2^m), ProverCommitSparse50.weight p (tail m a)*f (concat m n a suffix) := by
  classical
  rw [sum_concat]
  simp_rw [bits,append_weight,ProverCommitSparse50.boolean_weight]
  have he (b : Fin (2^n)) : tail n b=tail n suffix ↔ b=suffix := (ProverCommitBooleanEnum49.injective n).eq_iff
  simp only [he]
  apply Finset.sum_congr rfl
  intro a ha
  simp

#print axioms injective
#print axioms bijective
#print axioms sum_concat
#print axioms append_weight
#print axioms prune
end R1Z.ProverCommitSparseEnum50
