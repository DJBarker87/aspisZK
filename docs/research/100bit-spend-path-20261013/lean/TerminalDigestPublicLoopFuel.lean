import TerminalDigestPublicBranchRun
import OccupancyRangeTraversal
import TerminalDigestFrontierModel

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.Fuel
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
abbrev QM := field.QM31
abbrev Usize := UScalar UScalarTy.Usize
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Snapshot := pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Range := core.ops.range.Range Usize
private theorem bind_if {α β : Type} (p : Prop) [Decidable p]
    (a b : Result α) (f : α → Result β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split_ifs <;> rfl

private def decodedDigest (a : Array QM 8#usize) : R0P.Digest ExactQM :=
  fun j => AspisR1.ExtractedMaskQM31Exact.decode (cellAt a j.val)

/-- Bounded fuel theorem for the exact candidate source outer loop. Each
recursive step is the actual generated iterator step and actual branch body;
the model tracks the exact twenty-level frontier fold. -/
theorem loop_success_fuel
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (point : Array QM 10#usize) (selectors : Selectors) (source : Snapshot)
    (openings : Openings) (iter : Range) (fuel : Nat)
    (base digests : Array QM 8#usize)
    (hend : iter.end.val = 20) (hspan : iter.start.val + fuel = 20)
    (hsource : source = public1.transition.live_snapshot)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hopened : CanonicalArray openings.z)
    (hfrontierCanonical : ∀ k : Fin 20,
      AspisR1TerminalDigestPublicLoop.TargetActual.CanonicalM31
        (source.frontier.val[k.val]'(by
          simpa [source.frontier.property] using k.isLt)))
    (hbase : CanonicalArray base) (hdigests : CanonicalArray digests)
    (hmodel : decodedDigest digests =
      AspisR1TerminalDigestPublicLoop.Model.frontierPrefix
        (AspisR1.SemanticPublicModel.exactPublic public1)
        (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
        (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
        iter.start.val (decodedDigest base)) :
    ∃ out : Array QM 8#usize,
      AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop
        iter openings.z selectors digests source = .ok (out, source) ∧
      CanonicalArray out ∧
      decodedDigest out = AspisR1TerminalDigestPublicLoop.Model.frontierPrefix
        (AspisR1.SemanticPublicModel.exactPublic public1)
        (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
        (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
        20 (decodedDigest base) := by
  induction fuel generalizing iter digests with
  | zero =>
      have hstop : iter.start.val ≥ iter.end.val := by omega
      have hstart : iter.start.val = 20 := by omega
      have hnext := AspisR1.OccupancyRangeTraversal.next_done iter hstop
      refine ⟨digests, ?_, hdigests, ?_⟩
      · change AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop
          iter openings.z selectors digests source = .ok (digests, source)
        rw [AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop.eq_def]
        simp only [hnext, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      · rw [hstart] at hmodel
        simpa using hmodel
  | succ fuel ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hlevel : iter.start.val < 20 := by omega
      obtain ⟨iter1, hnext, hstart1, hend1, _⟩ :=
        AspisR1.OccupancyRangeTraversal.next_step iter hlt
      have hend1' : iter1.end.val = 20 := by rw [hend1, hend]
      have hspan1 : iter1.start.val + fuel = 20 := by omega
      obtain ⟨middle, hbranch, hmiddleCan, hstep⟩ :=
        AspisR1TerminalDigestPublicLoop.BranchRun.run_success public1 point selectors source
          iter.start hlevel openings digests hsource hpoint hbox hopened hdigests hfrontierCanonical
      have hmodel1 : decodedDigest middle =
          AspisR1TerminalDigestPublicLoop.Model.frontierPrefix
            (AspisR1.SemanticPublicModel.exactPublic public1)
            (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
            (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
            iter1.start.val (decodedDigest base) := by
        rw [hstart1]
        rw [AspisR1TerminalDigestPublicLoop.Model.frontierPrefix_succ
          (AspisR1.SemanticPublicModel.exactPublic public1)
          (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
          (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
          iter.start.val (decodedDigest base) hlevel]
        rw [← hmodel]
        exact hstep
      obtain ⟨out, hrec, houtCan, houtModel⟩ :=
        ih iter1 middle hend1' hspan1 hmiddleCan hmodel1
      have hcontinue0 := congrArg
        (fun result : Result (Array QM 8#usize) => do
          let d ← result
          AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop
            iter1 openings.z selectors d source) hbranch
      have hcontinue : (do
          let d ← AspisR1TerminalDigestPublicLoop.BranchRun.run
            iter.start source openings.z selectors digests
          AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop
            iter1 openings.z selectors d source) = .ok (out, source) := by
        calc
          _ = (do
            let d ← .ok middle
            AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop
              iter1 openings.z selectors d source) := hcontinue0
          _ = .ok (out, source) := by simpa only [bind_tc_ok] using hrec
        rfl
      refine ⟨out, ?_, houtCan, houtModel⟩
      change AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop
        iter openings.z selectors digests source = .ok (out, source)
      rw [AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop.eq_def]
      simp only [hnext, bind_tc_ok, Aeneas.Std.uncurry_apply_pair]
      simpa only [AspisR1TerminalDigestPublicLoop.BranchRun.run,
        bind_assoc_eq, bind_assoc, bind_if, bind_tc_ok] using hcontinue

/-- The exact source twenty-level outer call from index zero, preserving its
snapshot and implementing the retained symbolic frontier prefix. -/
theorem public_loop_success
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (point : Array QM 10#usize) (selectors : Selectors) (openings : Openings)
    (initial : Array QM 8#usize)
    (hsource : public1.transition.live_snapshot = public1.transition.live_snapshot)
    (hpoint : AspisR1.SelectorExpansionCorrectness.canonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hopened : CanonicalArray openings.z)
    (hfrontierCanonical : ∀ k : Fin 20,
      AspisR1TerminalDigestPublicLoop.TargetActual.CanonicalM31
        (public1.transition.live_snapshot.frontier.val[k.val]'(by
          simpa [public1.transition.live_snapshot.frontier.property] using k.isLt)))
    (hinitial : CanonicalArray initial) :
    ∃ middle,
      AspisR1TerminalDigestPublicLoop.Source.public_digest_lanes_loop
        { start := 0#usize, «end» := 20#usize }
        openings.z selectors initial public1.transition.live_snapshot =
          .ok (middle, public1.transition.live_snapshot) ∧
      CanonicalArray middle ∧
      decodedDigest middle = AspisR1TerminalDigestPublicLoop.Model.frontierPrefix
        (AspisR1.SemanticPublicModel.exactPublic public1)
        (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
        (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
        20 (decodedDigest initial) := by
  let iter : Range := { start := 0#usize, «end» := 20#usize }
  have hend : iter.end.val = 20 := by dsimp [iter]; scalar_tac
  have hspan : iter.start.val + 20 = 20 := by dsimp [iter]; scalar_tac
  have hmodel : decodedDigest initial =
      AspisR1TerminalDigestPublicLoop.Model.frontierPrefix
        (AspisR1.SemanticPublicModel.exactPublic public1)
        (AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings openings)
        (fun i => AspisR1.SelectorValueLaneModelComposition.pointSelector point i)
        iter.start.val (decodedDigest initial) := by simp [iter, AspisR1TerminalDigestPublicLoop.Model.frontierPrefix]
  obtain ⟨out, hrun, houtCan, houtModel⟩ := loop_success_fuel public1 point selectors
    public1.transition.live_snapshot openings iter 20 initial initial hend hspan
    hsource hpoint hbox hopened hfrontierCanonical hinitial hinitial hmodel
  exact ⟨out, by simpa [iter] using hrun, houtCan, houtModel⟩

#print axioms loop_success_fuel
#print axioms public_loop_success
end AspisR1TerminalDigestPublicLoop.Fuel
