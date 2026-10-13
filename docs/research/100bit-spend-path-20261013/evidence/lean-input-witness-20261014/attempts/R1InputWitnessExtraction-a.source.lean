import R1InputPairExtraction
import R1InputWitness

/-! One R1 joint-list candidate supplies the concrete input witness, output
notes, conserved bounded values, and chronological afterstate. All preceding
opening/semantic and source-state premises remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InputWitnessExtraction
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
      InputPairSelection.Facts pub (rowsOf rowEquiv m) ∧
      InputWitnessCore.Relation pub ((rowsOf rowEquiv m) 10 1008)
        (traceSk (rowsOf rowEquiv m)) (traceSalt (rowsOf rowEquiv m))
        (tracePath (rowsOf rowEquiv m)) (InputPair.leaf (rowsOf rowEquiv m)) := by
  obtain ⟨m, hm, hprod, hgates, hstate, hpair⟩ :=
    InputPairExtraction.strengthen_candidate_result pub W lam chi hshape leaves inv h
  exact ⟨m, hm, hprod, hgates, hstate, hpair,
    InputWitness.of_production pub (rowsOf rowEquiv m) lam chi hprod⟩

#print axioms strengthen_candidate_result
end AspisR1.InputWitnessExtraction
end
