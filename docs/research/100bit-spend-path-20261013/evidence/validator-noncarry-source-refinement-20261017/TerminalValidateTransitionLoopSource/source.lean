import OccupancyGeneratedSlice
import AspisR1SelectedMaskProbe.Funs
import EmptyRootSource
import CompositionPartsTailSource
import Aeneas.Std
import Aeneas.Tactic.RustAttributes

/- Exact validate_transition_loop source block from sealed terminal-indexed candidate
   Funs SHA 04fc129bbd54c8792d5c11e6c017e810cfc68d7a4a9577eca9455088ed04a42e.
   Namespaced cut only; empty_root targets its already retained exact source slice. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1TerminalValidateTransitionCandidate
open AspisR1SelectedMaskProbe

/-- Exact M31 comparison implementation from sealed candidate Funs lines 43–53. -/
def field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : field.M31) (other : field.M31) : Result Bool := do
  ok (self = other)

@[reducible]
impl_def field.M31.Insts.CoreCmpPartialEqM31 : core.cmp.PartialEq field.M31
  field.M31 := {
  eq := field.M31.Insts.CoreCmpPartialEqM31.eq
  ne := core.cmp.PartialEq.ne.trait_default field.M31.Insts.CoreCmpPartialEqM31
}

abbrev Error := AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::validate_transition]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 198:4-212:1 -/
@[rust_loop]
def validate_transition_loop
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (iter : core.ops.range.Range Std.Usize) (carry : Std.Usize) :
  Result (core.result.Result Unit
    Error)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (core.result.Result.Ok ())
  | some level =>
    if level = carry
    then
      if carry < 20#usize
      then
        validate_transition_loop public1
          iter1 carry
      else
        let (iter2, expected) ←
          if level < carry
          then
            do
            let expected1 ←
              AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
            ok (iter1, expected1)
          else
            do
            let i ←
              public1.transition.live_snapshot.next_pair_index >>> level
            let i1 ← lift (i &&& 1#u64)
            let a ←
              if i1 = 0#u64
              then AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
              else
                Array.index_usize public1.transition.live_snapshot.frontier
                  level
            ok (iter1, a)
        let a ←
          Array.index_usize
            public1.transition.candidate_afterstate.next_frontier level
        let b ←
          core.array.equality.PartialEqArray.ne
            field.M31.Insts.CoreCmpPartialEqM31 a expected
        if b
        then
          ok (core.result.Result.Err
            AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
        else
          validate_transition_loop
            public1 iter2 carry
    else
      let (iter2, expected) ←
        if level < carry
        then
          do
          let expected1 ←
            AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
          ok (iter1, expected1)
        else
          do
          let i ← public1.transition.live_snapshot.next_pair_index >>> level
          let i1 ← lift (i &&& 1#u64)
          let a ←
            if i1 = 0#u64
            then AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
            else
              Array.index_usize public1.transition.live_snapshot.frontier level
          ok (iter1, a)
      let a ←
        Array.index_usize public1.transition.candidate_afterstate.next_frontier
          level
      let b ←
        core.array.equality.PartialEqArray.ne
          field.M31.Insts.CoreCmpPartialEqM31 a expected
      if b
      then
        ok (core.result.Result.Err
          AspisR1CompositionTailCandidateTypes.pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
      else
        validate_transition_loop public1
          iter2 carry
partial_fixpoint
end AspisR1TerminalValidateTransitionCandidate
