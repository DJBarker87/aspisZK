import PV_EVH_EntropyReturnFootprint
import PV_EVH_EntropyCleanupCounts
set_option autoImplicit false
namespace PV_EVH_EntropyReturnComplete
open PV_EVH_StackZero (State)
open PV_EVH_EntropyCallerLayout (result mask)
open PV_EVH_EntropyReturnFootprint

/-- Join two symbolic sixteen-byte lanes. No array/recurrence normalization. -/
theorem lanes (m r : Nat → Nat) (dst src : Nat)
    (lo : ∀ i, i < 16 → m (dst+i) = r (src+i))
    (hi : ∀ i, i < 16 → m (dst+16+i) = r (src+16+i))
    (i : Nat) (h : i < 32) : m (dst+i) = r (src+i) := by
  by_cases small : i < 16
  · exact lo i small
  · have hd : dst+16+(i-16) = dst+i := by omega
    have hs : src+16+(i-16) = src+i := by omega
    simpa only [hd,hs] using hi (i-16) (by omega)

theorem payload (sp : Nat) (w : State) (i : Nat) (hi : i < 32) :
    (moved sp w).memory (result sp+1+i) = w.memory (mask sp+i) ∧
    (moved sp w).memory (result sp+33+i) = w.memory (sp+i) ∧
    (moved sp w).memory (result sp+65+i) = w.memory (sp+32+i) := by
  refine ⟨lanes _ _ _ _ (returnMaskLow_byte sp w) ?_ i hi,
    lanes _ _ _ _ (returnFieldLow_byte sp w) ?_ i hi,
    lanes _ _ _ _ (returnSeedLow_byte sp w) ?_ i hi⟩
  all_goals
    intro j hj
    first
    | simpa only [Nat.add_assoc,Nat.reduceAdd] using returnMaskHigh_byte sp w j hj
    | simpa only [Nat.add_assoc,Nat.reduceAdd] using returnFieldHigh_byte sp w j hj
    | simpa only [Nat.add_assoc,Nat.reduceAdd] using returnSeedHigh_byte sp w j hj

/-- All96 staging bytes survive the complete return stores. They are not
claimed unobservable, zero, or removed by returning the source value. -/
theorem staging (sp : Nat) (w : State) (i : Nat) (hi : i < 32) :
    (moved sp w).memory (sp+128+i) = w.memory (mask sp+i) ∧
    (moved sp w).memory (sp+160+i) = w.memory (sp+i) ∧
    (moved sp w).memory (sp+192+i) = w.memory (sp+32+i) := by
  refine ⟨lanes _ _ _ _ (stageMaskLow_byte sp w) ?_ i hi,
    lanes _ _ _ _ (stageFieldLow_byte sp w) ?_ i hi,
    lanes _ _ _ _ (stageSeedLow_byte sp w) ?_ i hi⟩
  all_goals
    intro j hj
    first
    | simpa only [Nat.add_assoc,Nat.reduceAdd] using stageMaskHigh_byte sp w j hj
    | simpa only [Nat.add_assoc,Nat.reduceAdd] using stageFieldHigh_byte sp w j hj
    | simpa only [Nat.add_assoc,Nat.reduceAdd] using stageSeedHigh_byte sp w j hj

def finish (owner sp : Nat) (w : State) : State :=
  PV_EVH_StackZero.drop (PV_EVH_EntropyDeployedLayout.original owner sp w) (moved sp w)

theorem cleanup_outside (owner sp p : Nat) (w : State) (hp : sp+64 ≤ p) :
    (finish owner sp w).memory p = (moved sp w).memory p :=
  PV_EVH_StackZero.outside_preserved _ _ p (Or.inr hp)

/-- Complete initialized return/tag footprint after ONLY original64 cleanup.
This remains a physical-memory interpretation. Lifetime transfer and actual
L3/advancing-world installation are not implied by these equalities. -/
theorem returned (owner sp : Nat) (w : State) (i : Nat) (hi : i < 32) :
    (finish owner sp w).memory (result sp) = 0 ∧
    (finish owner sp w).memory (result sp+1+i) = w.memory (mask sp+i) ∧
    (finish owner sp w).memory (result sp+33+i) = w.memory (sp+i) ∧
    (finish owner sp w).memory (result sp+65+i) = w.memory (sp+32+i) := by
  have hp (n : Nat) : sp+64 ≤ result sp+n := by
    unfold result PV_EVH_EntropyCallerLayout.caller
    omega
  rw [cleanup_outside owner sp _ w (by simpa using hp 0),
    cleanup_outside owner sp _ w (by have := hp (1+i); omega),
    cleanup_outside owner sp _ w (by have := hp (33+i); omega),
    cleanup_outside owner sp _ w (by have := hp (65+i); omega)]
  exact ⟨by simpa using tag_byte sp w 0 (by omega),payload sp w i hi⟩

theorem cleanup_staging (owner sp : Nat) (w : State) (i : Nat) (hi : i < 32) :
    (finish owner sp w).memory (sp+128+i) = w.memory (mask sp+i) ∧
    (finish owner sp w).memory (sp+160+i) = w.memory (sp+i) ∧
    (finish owner sp w).memory (sp+192+i) = w.memory (sp+32+i) := by
  rw [cleanup_outside owner sp _ w (by omega),
    cleanup_outside owner sp _ w (by omega),cleanup_outside owner sp _ w (by omega)]
  exact staging sp w i hi

theorem cleanup_original (owner sp : Nat) (w : State) (i : Nat) (hi : i < 64) :
    (finish owner sp w).memory (sp+i) = 0 :=
  PV_EVH_StackZero.dropped_cleared _ _ i hi

theorem cleanup_inner_residue (owner sp : Nat) (w : State) (i : Nat) (hi : i < 64) :
    (finish owner sp w).memory (sp+64+i) = w.memory (sp+64+i) := by
  rw [cleanup_outside owner sp _ w (by omega)]
  simpa only [Nat.add_assoc] using inner_residue sp w (64+i) (by omega)

#print axioms lanes
#print axioms payload
#print axioms staging
#print axioms cleanup_outside
#print axioms returned
#print axioms cleanup_staging
#print axioms cleanup_original
#print axioms cleanup_inner_residue
end PV_EVH_EntropyReturnComplete
