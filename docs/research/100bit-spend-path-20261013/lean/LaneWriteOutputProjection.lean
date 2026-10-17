import AspisR1PairForestLaneWriteSourceCut.Funs

open Aeneas Aeneas.Std Result

set_option autoImplicit false
namespace AspisR1PairForestLaneWriteSourceCut.OutputProjection

abbrev Lane := PoolV1PairForestLaneStateV1
abbrev Loop := next_pair_forest_lane_v1_loop
abbrev M31 := AspisR1PairForestLaneWriteSourceCut.M31

def CopiesAfterstate (result : PoolV1PairForestTerminalResultV1)
    (bump : Std.U8) (master : Array Std.U8 32#usize) (laneId : Std.U8)
    (out : Lane) : Prop :=
  out.bump = bump ∧ out.master = master ∧ out.lane_id = laneId ∧
  out.tree.next_leaf_index = result.verified_afterstate.next_pair_index ∧
  out.tree.root = result.verified_afterstate.next_root ∧
  out.tree.frontier = result.verified_afterstate.next_frontier

/-- Successful values of the extracted enumerate loop are precisely the lane
    constructor prescribed by the source afterstate. The theorem follows the
    actual loop equation and does not assume that the loop terminates. -/
theorem loop_success_copies_lane_and_afterstate
    (result : PoolV1PairForestTerminalResultV1)
    (iter : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter (Array M31 8#usize)))
    (bump : Std.U8) (master : Array Std.U8 32#usize) (laneId : Std.U8)
    (emptyRoots : Array (Array M31 8#usize) 21#usize) :
    ∀ out : Lane,
      Loop result iter bump master laneId emptyRoots =
        .ok (core.result.Result.Ok out) →
      CopiesAfterstate result bump master laneId out := by
  have hprop : ∀ iter,
      Loop result iter bump master laneId emptyRoots = .div ∨
      ∀ out : Lane,
        Loop result iter bump master laneId emptyRoots =
          .ok (core.result.Result.Ok out) →
        CopiesAfterstate result bump master laneId out := by
    apply AspisR1PairForestLaneWriteSourceCut.next_pair_forest_lane_v1_loop.fixpoint_induct result bump master laneId emptyRoots
      (motive := fun f => ∀ iter,
        f iter = .div ∨
        ∀ out : Lane,
          f iter = .ok (core.result.Result.Ok out) →
          CopiesAfterstate result bump master laneId out)
    · apply Lean.Order.admissible_pi_apply
        (fun (iter : core.iter.adapters.enumerate.Enumerate
            (core.slice.iter.Iter (Array M31 8#usize)))
          (r : Result (core.result.Result Lane PoolV1ProgramError)) =>
          r = .div ∨ ∀ out : Lane,
            r = .ok (core.result.Result.Ok out) →
            CopiesAfterstate result bump master laneId out)
      intro iter
      exact Lean.Order.admissible_flatOrder _ (Or.inl rfl)
    · intro f ih iter
      cases hn : core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter (Array M31 8#usize)) iter with
      | fail e =>
        right
        intro out hrun
        simp [hn] at hrun
      | div => left; simp [hn]
      | ok pair =>
        rcases pair with ⟨opt, iter1⟩
        cases opt with
        | none =>
          right
          intro out hrun
          -- The source `none` arm returns the literal lane constructor.
          simp only [hn, bind_tc_ok] at hrun
          cases hrun
          simp [CopiesAfterstate]
        | some p =>
          rcases p with ⟨level, node⟩
          cases hshift : result.verified_afterstate.next_pair_index >>> level with
          | fail e =>
            right
            intro out hrun
            simp [hn, bind_tc_ok, hshift] at hrun
          | div => left; simp [hn, bind_tc_ok, hshift]
          | ok shifted =>
            cases hbit : lift (shifted &&& 1#u64) with
            | fail e =>
              right
              intro out hrun
              simp [hn, bind_tc_ok, hshift, hbit] at hrun
            | div => left; simp [hn, bind_tc_ok, hshift, hbit]
            | ok bit =>
              by_cases hzero : bit = 0#u64
              · cases hread : Array.index_usize emptyRoots level with
                | fail e =>
                  right
                  intro out hrun
                  simp [hn, bind_tc_ok, hshift, hbit, hzero, hread] at hrun
                | div => left; simp [hn, bind_tc_ok, hshift, hbit, hzero, hread]
                | ok emptyRoot =>
                  cases hneq : core.array.equality.PartialEqArray.ne
                      M31.Insts.CoreCmpPartialEqM31 node emptyRoot with
                  | fail e =>
                    right
                    intro out hrun
                    simp [hn, bind_tc_ok, hshift, hbit, hzero, hread, hneq] at hrun
                  | div => left; simp [hn, bind_tc_ok, hshift, hbit, hzero, hread, hneq]
                  | ok mismatch =>
                    by_cases hmismatch : mismatch = true
                    · right
                      intro out hrun
                      simp [hn, bind_tc_ok, hshift, hbit, hzero, hread, hneq, hmismatch] at hrun
                    · right
                      intro out hrun
                      have hnext := ih iter1
                      simp [hn, bind_tc_ok, hshift, hbit, hzero, hread, hneq, hmismatch] at hrun
                      rcases hnext with hdiv | hgood
                      · simp [hrun] at hdiv
                      · exact hgood out hrun
              · right
                intro out hrun
                have hnext := ih iter1
                simp [hn, bind_tc_ok, hshift, hbit, hzero] at hrun
                rcases hnext with hdiv | hgood
                · simp [hrun] at hdiv
                · exact hgood out hrun
  intro out hrun
  rcases hprop iter with hdiv | hsuccess
  · simp [hrun] at hdiv
  · exact hsuccess out hrun

#print axioms loop_success_copies_lane_and_afterstate

end AspisR1PairForestLaneWriteSourceCut.OutputProjection
