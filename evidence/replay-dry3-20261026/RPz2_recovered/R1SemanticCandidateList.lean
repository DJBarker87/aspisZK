import R1MaskedSemantic

/-! Deterministic set-membership bridge between the R1 tuple alias and the
existing R0 committed-word list. No probability or uniqueness premise is used. -/
set_option autoImplicit false

namespace AspisR1.SemanticCandidateList

open AspisPool.AlgorithmicCircleDecoderV7

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E]

/-- `ConcreteBinding.candidates` and the frozen R0 `Lambda` use the identical
38230 joint-agreement filter. -/
theorem candidate_mem_iff_old_Lambda
    (W : Fin 29 → InitialWord E) (m : AspisR1.ConcreteBinding.Tuple E) :
    m ∈ AspisR1.ConcreteBinding.candidates W ↔
      m ∈ AspisR0.ListsResponses.Lambda W := by
  change m ∈ AspisR1.InitialResponses.Lambda W ↔
    m ∈ AspisR0.ListsResponses.Lambda W
  rfl

#print axioms candidate_mem_iff_old_Lambda

attribute [local irreducible] AspisR1.InitialResponses.Lambda
  AspisR0.ListsResponses.Lambda R0P.SemSource.LambdaRows

/-- Reindex an R1 candidate tuple into R0's semantic row trace. -/
theorem rowsOf_candidate_mem_LambdaRows
    (W : Fin 29 → InitialWord E) (m : AspisR1.ConcreteBinding.Tuple E)
    (pi : Fin 1024 ≃ Fin 1024)
    (hm : m ∈ AspisR1.ConcreteBinding.candidates W) :
    R0P.SemSource.rowsOf pi m ∈ R0P.SemSource.LambdaRows pi W := by
  apply (R0P.SemSource.mem_LambdaRows pi W (R0P.SemSource.rowsOf pi m)).mpr
  rw [R0P.SemSource.coeffsOf_rowsOf]
  exact (candidate_mem_iff_old_Lambda W m).mp hm

#print axioms rowsOf_candidate_mem_LambdaRows

end AspisR1.SemanticCandidateList
