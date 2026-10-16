import TerminalDigestPublicLoopSource
import AspisR1TerminalDigestBindingCandidate.LoopExact
import SemanticPublicModel
import ExtractedMaskQM31Exact
import R0P.Digest
import Aeneas.Tactic

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.FrontierTarget
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev M31 := field.M31
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact
abbrev Usize := UScalar UScalarTy.Usize

private theorem index_success {N : Usize} {α : Type} (a : Array α N)
    (i : Usize) (hi : i.val < N.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hb : i.val < a.length := by simpa [a.property] using hi
  obtain ⟨q, hread, hvalue⟩ := WP.spec_imp_exists (Array.index_usize_spec a i hb)
  rw [hread]
  congr 1

/-- The false branch's actual array read is exactly the retained public
snapshot frontier word, without unfolding or evaluating any frontier cells. -/
theorem source_frontier_target
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (source : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (level : Usize) (hlevel : level.val < 20)
    (hsource : source = public1.transition.live_snapshot)
    (expected : Array M31 8#usize)
    (hread : Array.index_usize source.frontier level = .ok expected)
    (hnotbit : ¬ R0P.digestBitZero
      (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩)
    (lane : Fin 8) :
    (AspisR1TerminalDigestBindingCandidate.LoopExact.targetValue expected false lane.val : ExactQM) =
      R0P.digestTarget (AspisR1.SemanticPublicModel.exactPublic public1)
        (.frontier ⟨level.val, hlevel⟩) lane := by
  have hsize : (20#usize).val = 20 := by scalar_tac
  have hb : level.val < (20#usize).val := by simpa [hsize] using hlevel
  have hget := index_success source.frontier level hb
  have hval : expected = source.frontier.val[level.val]'(by simpa [source.frontier.property] using hb) := by
    exact Result.ok.inj (hread.symm.trans hget)
  subst expected
  simp only [AspisR1TerminalDigestBindingCandidate.LoopExact.targetValue,
    dif_pos lane.isLt, Bool.false_eq_true, false_and, if_false,
    R0P.digestTarget, hnotbit]
  rw [hsource]
  rfl

#print axioms source_frontier_target
end AspisR1TerminalDigestPublicLoop.FrontierTarget
