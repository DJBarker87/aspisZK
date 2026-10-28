import Mathlib.Data.List.Sort
import Mathlib.Data.List.Dedup
namespace PV_B3P_Canonical133
set_option autoImplicit false

def canonical (xs : List Nat) : List Nat := (xs.mergeSort (fun a b => a ≤ b)).dedup

theorem canonical_eq (xs ys : List Nat) (sorted : ys.Pairwise (· < ·))
    (members : ∀ a, a ∈ xs ↔ a ∈ ys) : canonical xs = ys := by
  have hle : (canonical xs).Pairwise (· ≤ ·) :=
    (List.pairwise_mergeSort' (· ≤ ·) xs).sublist (List.dedup_sublist _)
  have hne : (canonical xs).Pairwise (· ≠ ·) := List.nodup_dedup _
  have hlt : (canonical xs).Pairwise (· < ·) :=
    (List.pairwise_and_iff.mpr ⟨hle,hne⟩).imp (fun {_ _} h => by omega)
  apply hlt.eq_of_mem_iff sorted
  intro a
  simpa only [canonical,List.mem_dedup,List.mem_mergeSort] using members a

-- Interval certificates compose by a named symbolic lemma. Only each small
-- block's own comparisons are reduced by the generator.
def Block (xs : List Nat) (lo hi : Nat) : Prop :=
  xs.Pairwise (· < ·) ∧ ∀ x ∈ xs, lo ≤ x ∧ x < hi

theorem join (xs ys : List Nat) (lo mid hi : Nat)
    (hx : Block xs lo mid) (hy : Block ys mid hi) (hl : lo ≤ mid) (hh : mid ≤ hi) : Block (xs ++ ys) lo hi := by
  constructor
  · apply List.pairwise_append.mpr
    refine ⟨hx.1,hy.1,?_⟩
    intro a ha b hb
    have := hx.2 a ha
    have := hy.2 b hb
    omega
  · intro x hmem
    rcases List.mem_append.mp hmem with h | h
    · have := hx.2 x h
      omega
    · have := hy.2 x h
      omega

#print axioms canonical_eq
#print axioms join
end PV_B3P_Canonical133
