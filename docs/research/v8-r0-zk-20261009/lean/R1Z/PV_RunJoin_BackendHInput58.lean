import R1Z.PV_RunJoin_BackendRawCoefficients58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendHInput58
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMatrix58 PV_RunJoin_BackendMRows58
abbrev Q := aspis_core.field.QM31

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (start first last : prover.Backend) (length : start.messages.length=29)
    (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (d g : Array Q 1024#usize) (h : Slice Q) (hh : h.length=1024)
    (root1 root2 : Array U8 32#usize)
    (hc1 : @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c1
      (types base) (selected base heap box ops) start columns d=ok (.Ok root1,first))
    (hc2 : @prover.Backend.Insts.Aspis_r1_cost_probeHost_semanticCommitments.c2
      (types base) (selected base heap box ops) first h g=ok (.Ok root2,last)) :
    let c := PV_RunJoin_BackendRawCoefficients58.coefficients columns hlen d h hh g
    (∀ l,l<29 → ∀ j,j<1024 → ProverCommitSubfieldOps47.Canonical (c l j)) ∧
    alloc.vec.Vec.deref last.messages=PV_RunJoin_CoefficientsWeight46.messages
      (fun l j => ProverRwDictionaryTower.fromW (ProverCommitNativeOps47.embedded (c l j))) ∧
    last.messages.length=29 := by
  dsimp only
  let p := PV_RunJoin_BackendRepresentation58.cells start.messages length
  have hp : start.messages=matrix p := (PV_RunJoin_BackendRepresentation58.of_vec start.messages length).symm
  have producer := PV_RunJoin_BackendFullProducer58.complete base heap box ops start first last p hp
    columns hlen d g h hh root1 root2 hc1 hc2
  rw [PV_RunJoin_BackendRawCoefficients58.matrix] at producer
  refine ⟨fun l _ j _ => PV_RunJoin_BackendRawCoefficients58.canonical columns hlen d h hh g l j,?_,?_⟩
  · rw [producer]
    exact PV_RunJoin_BackendMatrix58.deref _
  · rw [producer,PV_RunJoin_BackendMatrix58.length]

#print axioms complete
end R1Z.PV_RunJoin_BackendHInput58
