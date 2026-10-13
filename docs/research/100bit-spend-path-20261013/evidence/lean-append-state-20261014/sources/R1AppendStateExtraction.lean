import R1AppendExtraction
import R1AppendStateIndex

/-! The same R1 joint-list candidate now carries the chronological root and
saved-state invariant. Existing extraction premises, source guards, and the
old-state invariant remain explicit. This is not a Fiat--Shamir theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.AppendStateExtraction
open R0P R0P.SemSource AspisCircleGroupOrder AspisPool.IncrementalMerkleV1
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E] [CharP E P]

attribute [local irreducible] AspisR1.ConcreteBinding.candidates nodeCompress
  poseidonPermutation

theorem strengthen_candidate_result (pub : Public E)
    (W : Fin 29 → MatchingSupport.InitialWord E) (lam chi : E)
    (hshape : AppendSemantics.NonCarryShape pub) (leaves : List (Digest E))
    (inv : FrontierInvariant nodeCompress AppendTreeRoot.emptyPair 20 leaves
      (AppendTreeRoot.sourceFrontier pub))
    (h : ∃ m ∈ ConcreteBinding.candidates W,
      (ProductionHolds pub lam chi (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      AppendSemantics.GateFacts pub (rowsOf rowEquiv m)) :
    ∃ m ∈ ConcreteBinding.candidates W,
      (ProductionHolds pub lam chi (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      AppendSemantics.GateFacts pub (rowsOf rowEquiv m) ∧
      AppendTreeState.StateFacts pub (OutputNotes.output (rowsOf rowEquiv m) 33) leaves := by
  obtain ⟨m, hm, hprod, _⟩ := h
  exact ⟨m, hm, hprod,
    AppendTreeState.of_production pub (rowsOf rowEquiv m) lam chi hprod hshape leaves inv⟩

theorem continuing_candidate_result (pub next : Public E)
    (W : Fin 29 → MatchingSupport.InitialWord E) (lam chi : E)
    (hshape : AppendSemantics.NonCarryShape pub) (leaves : List (Digest E))
    (hi : pub.nextPairIndex < 2 ^ 20)
    (inv : FrontierInvariant nodeCompress AppendTreeRoot.emptyPair 20 leaves
      (AppendTreeRoot.sourceFrontier pub))
    (link : AppendStateIndex.StateLink pub next) (hnext : next.nextPairIndex < 2 ^ 20)
    (h : ∃ m ∈ ConcreteBinding.candidates W,
      (ProductionHolds pub lam chi (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      AppendSemantics.GateFacts pub (rowsOf rowEquiv m)) :
    ∃ m ∈ ConcreteBinding.candidates W,
      (ProductionHolds pub lam chi (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      AppendSemantics.GateFacts pub (rowsOf rowEquiv m) ∧
      AppendTreeState.StateFacts pub (OutputNotes.output (rowsOf rowEquiv m) 33) leaves ∧
      FrontierInvariant nodeCompress AppendTreeRoot.emptyPair 20
        (leaves ++ [OutputNotes.output (rowsOf rowEquiv m) 33])
        (AppendTreeRoot.sourceFrontier next) := by
  obtain ⟨m, hm, hprod, hgates, hstate⟩ :=
    strengthen_candidate_result pub W lam chi hshape leaves inv h
  exact ⟨m, hm, hprod, hgates, hstate,
    AppendStateIndex.next_invariant pub next _ leaves hi inv hstate link hnext⟩

#print axioms strengthen_candidate_result
#print axioms continuing_candidate_result
end AspisR1.AppendStateExtraction
end
