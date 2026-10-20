import QvStage2Count
import Mathlib.Data.Fintype.BigOperators

/-! Minimal retained privacy read-set definitions, to avoid rebuilding the
unrelated privacy game closure. crosscheck.py checks the definitions against
GamesR1PBin / LayoutR1P3Bin / EventsR1PBin. This is not an import of those
modules and does not discharge their ROpen or RComLog source premises. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QvStage2.RetainedPrivacy
open scoped BigOperators
attribute [local instance] Classical.propDecidable
abbrev Fib := Fin (2 ^ 18)
abbrev NodeIdx := Σ d : Fin 17, Fin (2 ^ (17 - d.val))
abbrev RIdx := Fin 2 ⊕ Fin 3 ⊕ (Fin 3 × Fib) ⊕ (Fin 3 × Fib) ⊕ (Fin 3 × NodeIdx)

def openedQ (fib : Fin 3 → Finset Fib) : Fin 3 ⊕ RIdx → Prop
  | .inl _ => True
  | .inr (.inr (.inr (.inr (.inl (T, u))))) => u ∈ fib T
  | .inr (.inr (.inr (.inr (.inr (T, n))))) => ∃ u ∈ fib T, u.val / 2 ^ (n.1.val + 1) = n.2.val
  | _ => False

def batchReadSet (fib : Fin 3 → Finset Fib) : Finset (Fin 3 ⊕ RIdx) :=
  Finset.univ.filter (openedQ fib)

/-- The 17 non-root parent levels. The three roots are separate positions. -/
def internalParents (fib : Fin 3 → Finset Fib) (T : Fin 3) : Finset NodeIdx :=
  Finset.univ.filter (fun n => ∃ u ∈ fib T,
    u.val / 2 ^ (n.1.val + 1) = n.2.val)

/-- Generic sum-carrier partition, proved before any concrete large carrier
is substituted. -/
theorem sum_filter_card {A B : Type} [Fintype A] [Fintype B]
    (p : A ⊕ B → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      (Finset.univ.filter (fun a => p (.inl a))).card +
      (Finset.univ.filter (fun b => p (.inr b))).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type]

theorem prod_filter_card {A B : Type} [Fintype A] [Fintype B]
    (p : A × B → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card =
      ∑ a, (Finset.univ.filter (fun b => p (a,b))).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

/-- Exact cardinality. Supplied bytes and padding add no positions. -/
theorem batch_card (fib : Fin 3 → Finset Fib) :
    (batchReadSet fib).card = 3 + (∑ T, (fib T).card) +
      ∑ T, (internalParents fib T).card := by
  simp only [batchReadSet, sum_filter_card, openedQ]
  simp only [prod_filter_card]
  simp [internalParents, Nat.add_assoc]

/-- Nodup and coverage are the exact hypotheses of the privacy batch_length
lemma, retained here without its unrelated game dependencies. -/
theorem batch_length (fib : Fin 3 → Finset Fib) (reads : List (Fin 3 ⊕ RIdx))
    (hn : reads.Nodup) (hc : ∀ c, c ∈ reads ↔ openedQ fib c) :
    reads.length = (batchReadSet fib).card := by
  have he : reads.toFinset = batchReadSet fib := by
    ext c
    simp only [List.mem_toFinset, batchReadSet, Finset.mem_filter,
      Finset.mem_univ, true_and, hc]
  rw [← he, List.toFinset_card_of_nodup hn]

/-- The named remaining geometry transport: the finite path union's leaf
and parent counts agree with the three occupied tries. No byte injectivity
or globally disjoint batches is assumed. -/
structure TrieTransport (fib : Fin 3 → Finset Fib) (a b c : QvStage1.Trie) : Prop where
  leaves : (∑ T, (fib T).card) = a.leaves + b.leaves + c.leaves
  parents : 3 + (∑ T, (internalParents fib T).card) = a.parents + b.parents + c.parents

theorem batchB_card_le (fib : Fin 3 → Finset Fib) (a b c : QvStage1.Trie)
    (transport : TrieTransport fib a b c)
    (hs : a.supplied + b.supplied + c.supplied ≤ 494)
    (hl : a.leaves + b.leaves + c.leaves ≤ 36) :
    (batchReadSet fib).card ≤ 563 := by
  have he := batch_card fib
  have hp := transport.parents
  have hc := QvStage2.batchB_reads_of_slots a b c hs hl
  rw [transport.leaves] at he
  omega

#print axioms sum_filter_card
#print axioms prod_filter_card
#print axioms batch_card
#print axioms batch_length
#print axioms batchB_card_le
end AspisR1.QvStage2.RetainedPrivacy
