import SemanticPackedBoundedSource

set_option autoImplicit false
namespace AspisR1.SemanticPackedBoundedFactoring
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev QM := field.QM31

def run (public1 : Public) (openings : Openings) (selectors : Selectors) :
    Result (Array QM 24#usize) := do
  let first4 ← SemanticPackedPrefix.run public1 openings selectors
  let digests ← DigestWrapperComposition.wrapper public1 openings selectors
  let packed ← AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
    first4 84#usize digests
  AspisR1ScalarSuffixCandidate.scalar_suffix packed public1 openings selectors

/-- This equality covers the complete caller, not just a vector assembly.
It retains the Result behavior of every family call and both packing suffixes. -/
theorem whole_caller_eq_factored (public1 : Public) (openings : Openings) (selectors : Selectors) :
    AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
      public1 openings selectors = run public1 openings selectors := by
  simp only [AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed,
    run, SemanticPackedPrefix.run, SemanticPackedPrefix.zero, DigestWrapperComposition.wrapper,
    AspisR1ScalarSuffixCandidate.scalar_suffix, bind_assoc_eq]
  all_goals rfl

#print axioms whole_caller_eq_factored
end AspisR1.SemanticPackedBoundedFactoring
