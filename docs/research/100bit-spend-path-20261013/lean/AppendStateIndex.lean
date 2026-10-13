import R1AppendTreeState
import R1FrontierIndex

/-! Initialization and continuation of the abstract state invariant. A link
states only that the next spend reads the saved index and frontier. Establishing
that link for Rust account reads/writes remains a source-refinement obligation. -/
set_option autoImplicit false
namespace AspisR1.AppendStateIndex
open R0P AspisCircleGroupOrder AspisPool.IncrementalMerkleV1
open AppendTreeRoot AppendFrontierShape AppendTreeState
variable {K : Type} [Field K] [CharP K P]

attribute [local irreducible] nodeCompress poseidonPermutation

theorem source_count (pub : Public K) (hi : pub.nextPairIndex < 2 ^ 20) :
    frontierValue (sourceFrontier pub) = pub.nextPairIndex := by
  exact FrontierIndex.indexedSlots_frontierValue_of_lt 20 pub.nextPairIndex
    pub.snapshotFrontier hi

theorem leaves_count (pub : Public K) (leaves : List (Digest K))
    (hi : pub.nextPairIndex < 2 ^ 20)
    (inv : FrontierInvariant nodeCompress emptyPair 20 leaves (sourceFrontier pub)) :
    leaves.length = pub.nextPairIndex := by
  exact inv.count_eq.symm.trans (source_count pub hi)

theorem initial_invariant (pub : Public K) (hi : pub.nextPairIndex = 0) :
    FrontierInvariant nodeCompress emptyPair 20 [] (sourceFrontier pub) := by
  have hf : sourceFrontier pub = List.replicate 20 none := by
    simp [sourceFrontier, frontierSlots, digestBitZero, hi]
  rw [hf]
  exact genesis_invariant nodeCompress emptyPair 20

structure StateLink (pub next : Public K) : Prop where
  index : next.nextPairIndex = pub.nextPairIndex + 1
  frontier : next.snapshotFrontier = pub.nextFrontier

theorem linked_frontier (pub next : Public K) (link : StateLink pub next) :
    sourceFrontier next = nextFrontier pub := by
  unfold sourceFrontier nextFrontier
  congr 1
  funext level
  simp only [frontierSlots, digestBitZero, nextSlots, link.index, link.frontier]

theorem full_index (pub : Public K) (leaf : Digest K) (leaves : List (Digest K))
    (hi : pub.nextPairIndex < 2 ^ 20)
    (inv : FrontierInvariant nodeCompress emptyPair 20 leaves (sourceFrontier pub))
    (state : StateFacts pub leaf leaves) (hc : digestCarry pub.nextPairIndex = 20) :
    pub.nextPairIndex + 1 = 2 ^ 20 := by
  have hl := leaves_count pub leaves hi inv
  have hfull := (state.full hc).1
  simp only [List.length_append, List.length_singleton, hl] at hfull
  exact hfull

/-- If the saved afterstate is a valid live source for a later spend, its
frontier authenticates exactly the old leaves followed by this new pair. -/
theorem next_invariant (pub next : Public K) (leaf : Digest K)
    (leaves : List (Digest K)) (hi : pub.nextPairIndex < 2 ^ 20)
    (inv : FrontierInvariant nodeCompress emptyPair 20 leaves (sourceFrontier pub))
    (state : StateFacts pub leaf leaves) (link : StateLink pub next)
    (hnext : next.nextPairIndex < 2 ^ 20) :
    FrontierInvariant nodeCompress emptyPair 20 (leaves ++ [leaf]) (sourceFrontier next) := by
  rw [linked_frontier pub next link]
  apply state.more
  by_contra hn
  have hc : digestCarry pub.nextPairIndex = 20 := by
    have := digest_carry_le pub.nextPairIndex
    omega
  have hfull := full_index pub leaf leaves hi inv state hc
  rw [link.index, hfull] at hnext
  exact Nat.lt_irrefl _ hnext

#print axioms source_count
#print axioms initial_invariant
#print axioms full_index
#print axioms next_invariant
end AspisR1.AppendStateIndex
