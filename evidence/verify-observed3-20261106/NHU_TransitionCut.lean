import NHU_TransitionWords
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_TransitionCut
open FIq_Native
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev RR := core.result.Result Unit pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
abbrev R := core.ops.range.Range Usize
def step (public1 : Public) (iter : R) (carry : Usize)
 (next : R→Result RR) : Result RR :=
do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (core.result.Result.Ok ())
  | some level =>
    if level = carry
    then
      if carry < 20#usize
      then
        next iter1
      else
        let (iter2, expected) ←
          if level < carry
          then
            do
            let expected1 ←
              pool_v1.pair_forest_semantic_terminal.empty_root level
            ok (iter1, expected1)
          else
            do
            let i ←
              public1.transition.live_snapshot.next_pair_index >>> level
            let i1 ← lift (i &&& 1#u64)
            let a ←
              if i1 = 0#u64
              then pool_v1.pair_forest_semantic_terminal.empty_root level
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
            pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
        else
          next iter2
    else
      let (iter2, expected) ←
        if level < carry
        then
          do
          let expected1 ←
            pool_v1.pair_forest_semantic_terminal.empty_root level
          ok (iter1, expected1)
        else
          do
          let i ← public1.transition.live_snapshot.next_pair_index >>> level
          let i1 ← lift (i &&& 1#u64)
          let a ←
            if i1 = 0#u64
            then pool_v1.pair_forest_semantic_terminal.empty_root level
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
          pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)
      else
        next iter2
theorem source (public1 : Public) (iter : R) (carry : Usize) :
 pool_v1.pair_forest_semantic_terminal.validate_transition_loop public1 iter carry=
 step public1 iter carry (fun next=>pool_v1.pair_forest_semantic_terminal.validate_transition_loop public1 next carry) := by
 rw [pool_v1.pair_forest_semantic_terminal.validate_transition_loop.eq_def]
 rfl
#print axioms source
end AspisR1.NHU_TransitionCut
end
