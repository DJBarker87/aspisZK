import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Card

/-! A miss-path theorem, not a source salt-obliviousness assumption in disguise.
The source adapter must exhibit one tree after fixing all non-target coins. -/
set_option autoImplicit false
namespace AspisV8R9

inductive ProbeTree (S : Type) where
  | stop : ProbeTree S
  | ask : S → ProbeTree S → ProbeTree S → ProbeTree S

variable {S : Type} [DecidableEq S]

def missSpine : ProbeTree S → List S
  | .stop => []
  | .ask guess _ no => guess :: missSpine no

def FirstHit (secret : S) : ProbeTree S → Prop
  | .stop => False
  | .ask guess _ no => secret = guess ∨ (secret ≠ guess ∧ FirstHit secret no)

theorem firstHit_iff_mem_spine (secret : S) (tree : ProbeTree S) :
    FirstHit secret tree ↔ secret ∈ missSpine tree := by
  induction tree with
  | stop => simp [FirstHit, missSpine]
  | ask guess yes no _ ih =>
      simp only [FirstHit, missSpine, List.mem_cons]
      by_cases equal : secret = guess
      · simp [equal]
      · simp [equal, ih]

def firstHitCandidates (tree : ProbeTree S) : Finset S :=
  (missSpine tree).toFinset

theorem firstHit_iff_mem_candidates (secret : S) (tree : ProbeTree S) :
    FirstHit secret tree ↔ secret ∈ firstHitCandidates tree := by
  simpa [firstHitCandidates] using firstHit_iff_mem_spine secret tree

theorem candidate_count_le_miss_path (tree : ProbeTree S) :
    (firstHitCandidates tree).card ≤ (missSpine tree).length := by
  exact List.toFinset_card_le _

theorem candidate_count_le_cap (tree : ProbeTree S) (q : Nat)
    (budget : (missSpine tree).length ≤ q) :
    (firstHitCandidates tree).card ≤ q :=
  (candidate_count_le_miss_path tree).trans budget

/-- Source interpretation obligation: for each omitted-coordinate tail and
fixed legal auxiliary tape, supply an independent tree and a first-hit
simulation. The conclusion then provides the finite candidate cover. -/
theorem source_hits_covered (tree : ProbeTree S) (hit : S → Prop)
    (refinement : ∀ secret, hit secret → FirstHit secret tree) :
    ∀ secret, hit secret → secret ∈ firstHitCandidates tree := by
  intro secret witnessed
  exact (firstHit_iff_mem_candidates secret tree).mp (refinement secret witnessed)

#print axioms firstHit_iff_mem_spine
#print axioms candidate_count_le_cap
#print axioms source_hits_covered
end AspisV8R9
