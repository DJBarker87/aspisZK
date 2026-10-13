import R1AppendExtraction
import R1AppendTreeRoot

/-! Strengthening of the same extracted R1 candidate with the chronological
post-append root, conditional only on the separately explicit authenticated
source-frontier invariant. Source correspondence and preservation of the
stored frontier representation remain outside this result. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.AppendTreeExtraction
open R0P R0P.SemSource AspisCircleGroupOrder AspisPool.IncrementalMerkleV1
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E] [CharP E P]

attribute [local irreducible] AspisR1.ConcreteBinding.candidates nodeCompress
  poseidonPermutation

theorem strengthen_candidate_result (pub : Public E)
    (W : Fin 29 → AspisR1.MatchingSupport.InitialWord E) (lam chi : E)
    (leaves : List (Digest E))
    (inv : FrontierInvariant nodeCompress AppendTreeRoot.emptyPair 20 leaves
      (AppendTreeRoot.sourceFrontier pub))
    (h : ∃ m ∈ AspisR1.ConcreteBinding.candidates W,
      (ProductionHolds pub lam chi (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      AppendSemantics.GateFacts pub (rowsOf rowEquiv m)) :
    ∃ m ∈ AspisR1.ConcreteBinding.candidates W,
      (ProductionHolds pub lam chi (rowsOf rowEquiv m) ∧
        CopyLinkBalance pub (rowsOf rowEquiv m)) ∧
      AppendSemantics.GateFacts pub (rowsOf rowEquiv m) ∧
      pub.nextRoot = rootWithEmptySuffix nodeCompress AppendTreeRoot.emptyPair 20
        (leaves ++ [OutputNotes.output (rowsOf rowEquiv m) 33]) := by
  obtain ⟨m, hm, hprod, hgates⟩ := h
  exact ⟨m, hm, hprod, hgates,
    AppendTreeRoot.next_root_correct pub (rowsOf rowEquiv m) lam chi hprod leaves inv⟩

#print axioms strengthen_candidate_result
end AspisR1.AppendTreeExtraction
end
