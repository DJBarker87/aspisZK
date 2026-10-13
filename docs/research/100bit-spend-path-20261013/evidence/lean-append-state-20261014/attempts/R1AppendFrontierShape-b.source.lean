import R1AppendBits
import R1AppendTreeRoot

/-! Convert the literal saved frontier into the option-valued chronological
tree model at the incremented index. The saved-frontier premise is the exact
conclusion of `AppendSemantics.afterstate_of_production`. -/
set_option autoImplicit false
namespace AspisR1.AppendFrontierShape
open R0P AspisPool.IncrementalMerkleV1 AppendTreeRoot AppendBits
variable {K : Type} [Field K]

attribute [local irreducible] nodeCompress poseidonPermutation

def nextSlots (pub : Public K) (level : Fin 20) : Option (Digest K) :=
  if (((pub.nextPairIndex + 1) >>> level.val) &&& 1) = 0 then none
  else some (pub.nextFrontier level)

def nextFrontier (pub : Public K) : List (Option (Digest K)) :=
  List.ofFn (nextSlots pub)

theorem slots_correct (pub : Public K) (leaf : Digest K)
    (hf : pub.nextFrontier = AppendSemantics.expectedFrontier pub leaf)
    (level : Fin 20) :
    nextSlots pub level =
      if level.val < digestCarry pub.nextPairIndex then none
      else if level.val = digestCarry pub.nextPairIndex
      then some (AppendPath.pathPrefix pub leaf (digestCarry pub.nextPairIndex))
      else frontierSlots pub level := by
  have hb := increment_bits 20 pub.nextPairIndex level.val level.isLt
  change BitZero (pub.nextPairIndex + 1) level.val ↔
    level.val < digestCarry pub.nextPairIndex ∨
      (digestCarry pub.nextPairIndex < level.val ∧ digestBitZero pub level) at hb
  unfold nextSlots
  by_cases hl : level.val < digestCarry pub.nextPairIndex
  · rw [if_pos (hb.mpr (Or.inl hl)), if_pos hl]
  · rw [if_neg hl]
    by_cases he : level.val = digestCarry pub.nextPairIndex
    · have hn : ¬ BitZero (pub.nextPairIndex + 1) level.val := by
        intro h
        have := hb.mp h
        omega
      rw [if_neg hn, if_pos he, hf]
      simp only [AppendSemantics.expectedFrontier, if_pos he, he]
    · have hg : digestCarry pub.nextPairIndex < level.val := by omega
      rw [if_neg he]
      unfold frontierSlots
      by_cases hz : digestBitZero pub level
      · rw [if_pos hz, if_pos (hb.mpr (Or.inr ⟨hg, hz⟩))]
      · have hn : ¬ BitZero (pub.nextPairIndex + 1) level.val := by
          intro h
          exact (hb.mp h).elim hl (fun h => hz h.2)
        rw [if_neg hn, if_neg hz, hf]
        simp only [AppendSemantics.expectedFrontier, if_neg he,
          or_self_iff, hl, hz, if_false]

theorem empty_inactive (pub : Public K) (leaf : Digest K)
    (hf : pub.nextFrontier = AppendSemantics.expectedFrontier pub leaf)
    (level : Fin 20) (hz : BitZero (pub.nextPairIndex + 1) level.val) :
    pub.nextFrontier level = AppendNode.frozenEmpty level.castSucc := by
  have hb := (increment_bits 20 pub.nextPairIndex level.val level.isLt).mp hz
  change level.val < digestCarry pub.nextPairIndex ∨
    (digestCarry pub.nextPairIndex < level.val ∧ digestBitZero pub level) at hb
  have hn : level.val ≠ digestCarry pub.nextPairIndex := by omega
  have hempty : level.val < digestCarry pub.nextPairIndex ∨ digestBitZero pub level := by
    exact hb.elim Or.inl (fun h => Or.inr h.2)
  rw [hf]
  simp only [AppendSemantics.expectedFrontier, if_neg hn, if_pos hempty]

theorem full_frontier_empty (pub : Public K) (leaf : Digest K)
    (hf : pub.nextFrontier = AppendSemantics.expectedFrontier pub leaf)
    (hc : digestCarry pub.nextPairIndex = 20) :
    (∀ level : Fin 20, pub.nextFrontier level = AppendNode.frozenEmpty level.castSucc) ∧
      nextFrontier pub = List.replicate 20 none := by
  have hz : ∀ level : Fin 20, BitZero (pub.nextPairIndex + 1) level.val := by
    intro level
    apply (increment_bits 20 pub.nextPairIndex level.val level.isLt).mpr
    left
    change level.val < digestCarry pub.nextPairIndex
    rw [hc]
    exact level.isLt
  constructor
  · intro level
    exact empty_inactive pub leaf hf level (hz level)
  · unfold nextFrontier
    have he : nextSlots pub = fun _ => none := by
      funext level
      exact if_pos (hz level)
    rw [he]
    simp

#print axioms slots_correct
#print axioms empty_inactive
#print axioms full_frontier_empty
end AspisR1.AppendFrontierShape
