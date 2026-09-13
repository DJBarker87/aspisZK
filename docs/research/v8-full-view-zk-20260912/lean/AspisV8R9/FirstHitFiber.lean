import AspisV8R9.FirstHit
import AspisV8PairedCommitment.SaltCounting
import Mathlib.Data.Set.PowersetCard

/-!
# First-hit certificates discharge the R8 coordinate premise

This is only the finite counting adapter.  The source layer must still build
one probe tree after fixing the omitted-coordinate tail and prove the
refinement premise for the actual execution.
-/
set_option autoImplicit false
namespace AspisV8R9
open AspisV8PairedCommitment

noncomputable section
variable {S : Type} [Fintype S] [DecidableEq S]

abbrev UnorderedPair (α : Type*) [DecidableEq α] := Set.powersetCard α 2

theorem unorderedPair_card (α : Type*) [Fintype α] [DecidableEq α] :
    Nat.card (UnorderedPair α) = (Fintype.card α).choose 2 := by
  rw [Fintype.card_eq_nat_card]
  exact Set.powersetCard.card (α := α) (n := 2)

private def hitToCandidate (tree : ProbeTree S) (hit : S → Prop)
    (refinement : ∀ secret, hit secret → FirstHit secret tree) :
    {secret : S // hit secret} → {secret : S // secret ∈ firstHitCandidates tree} :=
  fun secret => ⟨secret.1,
    source_hits_covered tree hit refinement secret.1 secret.2⟩

private theorem hitToCandidate_injective (tree : ProbeTree S) (hit : S → Prop)
    (refinement : ∀ secret, hit secret → FirstHit secret tree) :
    Function.Injective (hitToCandidate tree hit refinement) := by
  intro left right equal
  exact Subtype.ext (congrArg
    (fun value : {secret : S // secret ∈ firstHitCandidates tree} => value.1) equal)

theorem firstHit_fiber_card_le (tree : ProbeTree S) (hit : S → Prop) (q : Nat)
    (refinement : ∀ secret, hit secret → FirstHit secret tree)
    (budget : (missSpine tree).length ≤ q) :
    Nat.card {secret : S // hit secret} ≤ q := by
  calc
    Nat.card {secret : S // hit secret} ≤
        Nat.card {secret : S // secret ∈ firstHitCandidates tree} :=
      Nat.card_le_card_of_injective (hitToCandidate tree hit refinement)
        (hitToCandidate_injective tree hit refinement)
    _ = (firstHitCandidates tree).card := by simp
    _ ≤ q := candidate_count_le_cap tree q budget

variable {Slot : Type*} {Salt : Type}
  [Fintype Slot] [DecidableEq Slot]
  [Fintype Salt] [DecidableEq Salt] [Nonempty Salt]

/-- Exact adapter required by `ideal_bad_count_le`.  Its refinement premise is
the named source-specific obligation; neither the final bad mass nor salt
obliviousness is assumed here. -/
theorem coordinate_fiber_cap_of_firstHit
    (probe : Slot → SaltVector Slot Salt → Prop) (q : Nat)
    (tree : ∀ i, OmitCoordinate (Salt := Salt) i → ProbeTree Salt)
    (refinement : ∀ i tail secret,
      probe i (rebuildCoordinate i secret tail) → FirstHit secret (tree i tail))
    (budget : ∀ i tail, (missSpine (tree i tail)).length ≤ q) :
    ∀ i tail, Nat.card (coordinateFiber probe i tail) ≤ q := by
  intro i tail
  exact firstHit_fiber_card_le (tree i tail)
    (fun secret => probe i (rebuildCoordinate i secret tail)) q
    (refinement i tail) (budget i tail)

#print axioms firstHit_fiber_card_le
#print axioms coordinate_fiber_cap_of_firstHit
#print axioms unorderedPair_card
end
end AspisV8R9
