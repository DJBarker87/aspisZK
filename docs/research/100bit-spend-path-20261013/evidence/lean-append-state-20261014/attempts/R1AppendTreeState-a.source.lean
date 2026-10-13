import R1AppendCarryIndexed
import R1AppendFrontierShape

/-! Preservation of the chronological frontier invariant. This uses the
existing authenticated old-state invariant and the literal non-carry guard;
neither a post-state invariant nor an append-result equality is assumed. -/
set_option autoImplicit false
namespace AspisR1.AppendTreeState
open R0P AspisCircleGroupOrder AspisPool.IncrementalMerkleV1
open AppendTreeRoot AppendFrontierShape
variable {K : Type} [Field K]

attribute [local irreducible] nodeCompress poseidonPermutation

theorem below_carry (pub : Public K) (leaf : Digest K) (level : Fin 20)
    (hl : level.val < digestCarry pub.nextPairIndex) :
    ∃ left, frontierSlots pub level = some left ∧
      AppendPath.pathPrefix pub leaf (level.val + 1) =
        nodeCompress left (AppendPath.pathPrefix pub leaf level.val) := by
  have hb : ¬ digestBitZero pub level :=
    AppendBits.before_carry 20 pub.nextPairIndex level.val hl
  refine ⟨pub.snapshotFrontier level, ?_, ?_⟩
  · exact if_neg hb
  · rw [AppendPath.pathPrefix, dif_pos level.isLt]
    exact if_neg hb

theorem carry_empty (pub : Public K) (hc : digestCarry pub.nextPairIndex < 20) :
    frontierSlots pub ⟨digestCarry pub.nextPairIndex, hc⟩ = none := by
  exact if_pos (AppendBits.at_carry 20 pub.nextPairIndex hc)

theorem append_more (pub : Public K) (leaf : Digest K)
    (hf : pub.nextFrontier = AppendSemantics.expectedFrontier pub leaf)
    (hc : digestCarry pub.nextPairIndex < 20) :
    appendCarry nodeCompress leaf (sourceFrontier pub) = .more (nextFrontier pub) := by
  have h := appendCarry_indexed_more nodeCompress (digest_carry_le pub.nextPairIndex) hc
    (frontierSlots pub) (AppendPath.pathPrefix pub leaf)
    (below_carry pub leaf) (carry_empty pub)
  have he : nextSlots pub = fun level : Fin 20 =>
      if level.val < digestCarry pub.nextPairIndex then none
      else if level.val = digestCarry pub.nextPairIndex
      then some (AppendPath.pathPrefix pub leaf (digestCarry pub.nextPairIndex))
      else frontierSlots pub level := by
    funext level
    exact slots_correct pub leaf hf level
  change appendCarry nodeCompress (AppendPath.pathPrefix pub leaf 0)
    (List.ofFn (frontierSlots pub)) = .more (List.ofFn (nextSlots pub))
  rw [he]
  exact h

theorem append_full (pub : Public K) (leaf : Digest K)
    (hc : digestCarry pub.nextPairIndex = 20) :
    appendCarry nodeCompress leaf (sourceFrontier pub) =
      .full (AppendPath.pathPrefix pub leaf 20) := by
  exact appendCarry_indexed_full nodeCompress (digest_carry_le pub.nextPairIndex) hc
    (frontierSlots pub) (AppendPath.pathPrefix pub leaf)
    (below_carry pub leaf) (carry_empty pub)

variable [CharP K P]

structure StateFacts (pub : Public K) (leaf : Digest K) (leaves : List (Digest K)) : Prop where
  root : pub.nextRoot = rootWithEmptySuffix nodeCompress emptyPair 20 (leaves ++ [leaf])
  inactive : ∀ level : Fin 20, AppendBits.BitZero (pub.nextPairIndex + 1) level.val →
    pub.nextFrontier level = AppendNode.frozenEmpty level.castSucc
  more : digestCarry pub.nextPairIndex < 20 →
    FrontierInvariant nodeCompress emptyPair 20 (leaves ++ [leaf]) (nextFrontier pub)
  full : digestCarry pub.nextPairIndex = 20 →
    (leaves ++ [leaf]).length = 2 ^ 20 ∧
      (∀ level : Fin 20, pub.nextFrontier level = AppendNode.frozenEmpty level.castSucc) ∧
      nextFrontier pub = List.replicate 20 none

theorem of_production (pub : Public K) (A : Trace K) (lam chi : K)
    (hprod : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A)
    (hshape : AppendSemantics.NonCarryShape pub)
    (leaves : List (Digest K))
    (inv : FrontierInvariant nodeCompress emptyPair 20 leaves (sourceFrontier pub)) :
    AppendSemantics.GateFacts pub A ∧ StateFacts pub (OutputNotes.output A 33) leaves := by
  obtain ⟨gates, hf⟩ := AppendSemantics.afterstate_of_production P rfl pub A lam chi hprod hshape
  refine ⟨gates, ⟨next_root_correct pub A lam chi hprod leaves inv,
    empty_inactive pub _ hf, ?_, ?_⟩⟩
  · intro hc
    exact FrontierInvariant.append_preserves nodeCompress emptyPair _ 20 leaves
      (sourceFrontier pub) (nextFrontier pub) inv (append_more pub _ hf hc)
  · intro hc
    have ht := append_terminal_correct nodeCompress emptyPair (OutputNotes.output A 33)
      20 leaves (sourceFrontier pub) (AppendPath.pathPrefix pub (OutputNotes.output A 33) 20)
      inv (append_full pub _ hc)
    exact ⟨ht.1, full_frontier_empty pub _ hf hc⟩

#print axioms below_carry
#print axioms append_more
#print axioms append_full
#print axioms of_production
end AspisR1.AppendTreeState
