import R1AppendStateExtraction
import R1InputPairSelection

/-! Input-pair occupancy and selected-commitment facts on the same R1
candidate that supplies the output notes and chronological afterstate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InputPairExtraction
open R0P R0P.SemSource AspisCircleGroupOrder AspisPool.IncrementalMerkleV1
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E] [CharP E P]

attribute [local irreducible] ConcreteBinding.candidates nodeCompress poseidonPermutation

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
      AppendTreeState.StateFacts pub (OutputNotes.output (rowsOf rowEquiv m) 33) leaves ∧
      InputPairSelection.Facts pub (rowsOf rowEquiv m) := by
  obtain ⟨m, hm, hprod, hgates, hstate⟩ :=
    AppendStateExtraction.strengthen_candidate_result pub W lam chi hshape leaves inv h
  exact ⟨m, hm, hprod, hgates, hstate,
    InputPairSelection.of_production pub (rowsOf rowEquiv m) lam chi hprod⟩

#print axioms strengthen_candidate_result
end AspisR1.InputPairExtraction
end
