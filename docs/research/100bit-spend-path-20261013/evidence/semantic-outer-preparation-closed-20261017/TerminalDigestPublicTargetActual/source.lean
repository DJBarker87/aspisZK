import TerminalDigestFrontierTarget
import EmptyRootBindingModel
import AspisR1TerminalDigestBindingCandidate.LoopExact

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.TargetActual
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1TerminalDigestBindingCandidate.LoopExact
abbrev M31 := field.M31
abbrev Usize := UScalar UScalarTy.Usize
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev CanonicalM31 (a : Array M31 8#usize) :=
  ∀ lane : Fin 8, (a.val[lane.val]'(by simpa [a.property] using lane.isLt)).val <
    AspisR1.ExtractedMaskTowerAdd.P

/-- Derive the branch target and canonical M31 input from the exact source
operand: empty_root on the true branch, or the live snapshot frontier read on
the false branch. -/
theorem source_target
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (source : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (level : Usize) (hlevel : level.val < 20)
    (hsource : source = public1.transition.live_snapshot)
    (expected : Array M31 8#usize) (rightTweak : Bool)
    (hbranch : rightTweak = true ↔ R0P.digestBitZero
      (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩)
    (hfrontierCanonical : ∀ k : Fin 20, CanonicalM31
      (source.frontier.val[k.val]'(by
        simpa [source.frontier.property] using k.isLt)))
    (hactual : (if rightTweak then
        AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level
      else Array.index_usize source.frontier level) = .ok expected) :
    CanonicalM31 expected ∧
      ∀ lane : Fin 8,
        (targetValue expected rightTweak lane.val : ExactQM) =
          R0P.digestTarget (AspisR1.SemanticPublicModel.exactPublic public1)
            (.frontier ⟨level.val, hlevel⟩) lane := by
  by_cases hr : rightTweak
  · have hroot := AspisR1.EmptyRootBindingModel.source_right_target level hlevel
    rcases hroot with ⟨root, hrootRun, hrootCan, hrootTarget⟩
    have hactual' :
        AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level =
          .ok expected := by
      simpa [hr] using hactual
    have heq : expected = root := Result.ok.inj (hactual'.symm.trans hrootRun)
    subst expected
    constructor
    · exact hrootCan
    · intro lane
      have hbit := hbranch.mp hr
      rw [R0P.digestTarget, if_pos hbit]
      simpa [hr] using hrootTarget lane
  · have hfalse : rightTweak = false := Bool.eq_false_iff.mpr hr
    have hread : Array.index_usize source.frontier level = .ok expected := by
      simpa [hfalse] using hactual
    have hnotbit : ¬ R0P.digestBitZero
        (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩ := by
      intro hb
      exact hr (hbranch.mpr hb)
    have hsize : (20#usize).val = 20 := by scalar_tac
    have hbound : level.val < (20#usize).val := by simpa [hsize] using hlevel
    have hlen : level.val < source.frontier.length := by
      simpa [source.frontier.property] using hbound
    obtain ⟨q, hreadQ, hqvalue⟩ :=
      WP.spec_imp_exists (Array.index_usize_spec source.frontier level hlen)
    have heq : expected = q := Result.ok.inj (hread.symm.trans hreadQ)
    subst expected
    have hqEq : q = source.frontier.val[level.val]'(by
        simpa [source.frontier.property] using hbound) := by
      simpa using hqvalue
    have hcanonical : CanonicalM31 q := by
      intro lane
      rw [hqEq]
      exact hfrontierCanonical ⟨level.val, hlevel⟩ lane
    constructor
    · exact hcanonical
    · intro lane
      simpa [hfalse] using
        (AspisR1TerminalDigestPublicLoop.FrontierTarget.source_frontier_target
          public1 source level hlevel hsource q hreadQ hnotbit lane)

#print axioms source_target
end AspisR1TerminalDigestPublicLoop.TargetActual
