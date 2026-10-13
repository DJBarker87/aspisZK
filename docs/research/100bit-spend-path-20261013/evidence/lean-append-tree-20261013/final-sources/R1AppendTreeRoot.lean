import R1FrozenEmptyRoots
import R1ReconstructChain
import R1AppendSemantics

/-! Root correspondence with the existing chronological tree model. The
incoming authenticated frontier invariant remains explicit. Both ordinary
and full-capacity append outcomes are included by append_reconstruct_afterstate.
This does not establish the public codec, Rust refinement, or preservation of
every stored next-frontier cell. -/
set_option autoImplicit false
namespace AspisR1.AppendTreeRoot
open R0P AspisCircleGroupOrder AspisPool.IncrementalMerkleV1
variable {K : Type} [Field K] [CharP K P]

attribute [local irreducible] nodeCompress poseidonPermutation

def emptyPair : Digest K := nodeCompress (fun _ => 0) (fun _ => 0)

def frontierSlots (pub : Public K) (level : Fin 20) : Option (Digest K) :=
  if digestBitZero pub level then none else some (pub.snapshotFrontier level)

def sourceFrontier (pub : Public K) : List (Option (Digest K)) :=
  List.ofFn (frontierSlots pub)

theorem frozen_recursive (n : Nat) (hn : n ≤ 20) :
    AppendNode.frozenEmpty (K := K) ⟨n, by omega⟩ =
      recursiveEmptyRoot nodeCompress emptyPair n := by
  induction n with
  | zero => exact FrozenEmptyRoots.initial
  | succ n ih =>
    have hs := FrozenEmptyRoots.successor (K := K) ⟨n, by omega⟩
    change AppendNode.frozenEmpty (K := K) ⟨n+1, by omega⟩ =
      nodeCompress (AppendNode.frozenEmpty ⟨n, by omega⟩)
        (AppendNode.frozenEmpty ⟨n, by omega⟩) at hs
    rw [hs, ih (by omega)]
    rfl

theorem path_reconstruct (pub : Public K) (leaf : Digest K) :
    AppendPath.pathPrefix pub leaf 20 =
      reconstructFrom nodeCompress emptyPair 0 leaf (sourceFrontier pub) := by
  symm
  apply reconstruct_ofFn_chain nodeCompress emptyPair 20 0
    (AppendPath.pathPrefix pub leaf) (frontierSlots pub)
  intro i
  rw [AppendPath.pathPrefix, dif_pos i.isLt]
  unfold AppendPath.step frontierSlots
  by_cases hz : digestBitZero pub i
  · rw [if_pos hz, if_pos hz]
    simp only [Nat.zero_add]
    rw [← frozen_recursive i.val (by omega)]
    rfl
  · rw [if_neg hz, if_neg hz]

/-- The source invariant is about the old frontier and leaf sequence only.
No equality for the new root or post-append tree is assumed. -/
theorem next_root_correct (pub : Public K) (A : Trace K) (lam chi : K)
    (hprod : ProductionHolds pub lam chi A ∧ CopyLinkBalance pub A)
    (leaves : List (Digest K))
    (inv : FrontierInvariant nodeCompress emptyPair 20 leaves (sourceFrontier pub)) :
    pub.nextRoot = rootWithEmptySuffix nodeCompress emptyPair 20
      (leaves ++ [OutputNotes.output A 33]) := by
  have gates := AppendSemantics.of_production P rfl pub A lam chi hprod
  rw [gates.root, path_reconstruct]
  exact append_reconstruct_afterstate nodeCompress emptyPair (OutputNotes.output A 33)
    20 leaves (sourceFrontier pub) inv

#print axioms frozen_recursive
#print axioms path_reconstruct
#print axioms next_root_correct
end AspisR1.AppendTreeRoot
