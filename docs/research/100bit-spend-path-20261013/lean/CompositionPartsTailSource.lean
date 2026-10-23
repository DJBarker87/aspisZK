import Aeneas
import ImportUnionNamedDiscriminant
import Aeneas.Tactic.RustAttributes
import TerminalCompositionPolynomial
import SelectedClaimProofs

/-! Exact post-copy tail of the retained composition_parts source. Local
parameters are the values bound before the source cut; reachability and source
binding of those inputs are separate enclosing-caller obligations. -/
set_option autoImplicit false
namespace AspisR1CompositionTailCandidateTypes
open Aeneas Aeneas.Std Result
@[import_union_discriminant isize]
inductive pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
  where
| InvalidPublicAmount :
  pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
| InvalidAppendTransition :
  pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
end AspisR1CompositionTailCandidateTypes

namespace AspisR1.CompositionPartsTail
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Error := AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
abbrev Output := QM × (Array QM 16#usize) × (Array QM 10#usize) × QM × QM × QM

def run (semantic : Array QM 24#usize) (poseidon : Array QM 4#usize)
    (theta seed active : QM) (claims : Array QM 84#usize)
    (a : Array QM 16#usize) (mask_only : Array QM 10#usize) (h1_z : QM) :
    Result (core.result.Result Output Error) := do
  let prepared_theta ← field.PreparedQm31Multiplier.new theta
  let s ← lift (Array.to_slice semantic)
  let i1 := Slice.len s
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) { start := 0#usize, «end» := i1 }
  let composition ←
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iter
      semantic prepared_theta seed
  let s1 ← lift (Array.to_slice poseidon)
  let i2 := Slice.len s1
  let iter1 ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) { start := 0#usize, «end» := i2 }
  let composition1 ←
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iter1
      poseidon prepared_theta composition
  let i3 ← pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
  let q ←
    pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize i3
  ok (core.result.Result.Ok (composition1, a, mask_only, q, h1_z,
    active))

end AspisR1.CompositionPartsTail
