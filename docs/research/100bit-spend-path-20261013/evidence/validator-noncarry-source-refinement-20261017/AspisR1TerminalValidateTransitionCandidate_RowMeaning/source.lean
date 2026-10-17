import AspisR1TerminalValidateTransitionCandidate.ExpectedAt
import TerminalDigestPublicBranchModel
import EmptyRootBindingModel
import SemanticPublicModel
import R0P.Digest
import Aeneas.Tactic

set_option autoImplicit false
namespace AspisR1TerminalValidateTransitionCandidate
namespace RowMeaning
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1TerminalValidateTransitionCandidate
open AspisR1TerminalValidateTransitionCandidate.ExpectedAt
abbrev Usize := UScalar UScalarTy.Usize
abbrev M31 := field.M31
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev ExactQM := AspisR1.ExtractedMaskQM31Exact.QM31Exact

def frozenEmptyModel (level : Fin 21) : R0P.Digest ExactQM :=
  fun lane => (R0P.emptyRootsNat level lane : ExactQM)

/-- Interpret the exact checked row operand as the frozen empty row below the
carry boundary, or as the source-selected empty/frontier row above it. -/
theorem expectedAt_matches_noncarry_model
    (public1 : Public) (carry level : Usize) (hlevel : level.val < 20)
    (expected : Array M31 8#usize)
    (hexpected : expectedAt public1 level carry = .ok expected) :
    AspisR1.SemanticPublicModel.digest expected =
      if level.val < carry.val ∨ R0P.digestBitZero
          (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩
      then frozenEmptyModel ⟨level.val, by omega⟩
      else (AspisR1.SemanticPublicModel.exactPublic public1).snapshotFrontier
        ⟨level.val, hlevel⟩ := by
  by_cases hlow : level.val < carry.val
  · have hlowU : level < carry := by change level.val < carry.val; exact hlow
    have htmp := hexpected
    unfold expectedAt at htmp
    rw [if_pos hlowU] at htmp
    obtain ⟨root, hroot, hcanonical, hvalues⟩ :=
      AspisR1.EmptyRootBindingModel.source_root_canonical level (by omega)
    have hrootEq : expected = root := Result.ok.inj (htmp.symm.trans hroot)
    subst expected
    rw [if_pos (Or.inl hlow)]
    funext lane
    simp [AspisR1.SemanticPublicModel.digest,
      frozenEmptyModel, hvalues lane]
  · have hhighU : ¬ level < carry := by
      intro h
      exact hlow (by change level.val < carry.val at h; exact h)
    obtain ⟨shifted, bit, hshift, hbit, hbitModel⟩ :=
      AspisR1TerminalDigestPublicLoop.BranchModel.live_snapshot_branch
        public1 level hlevel
    have htmp := hexpected
    unfold expectedAt at htmp
    rw [if_neg hhighU] at htmp
    simp only [hshift, hbit, bind_tc_ok] at htmp
    by_cases hzero : bit = 0#u64
    · have hbitZero : R0P.digestBitZero
          (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩ :=
        hbitModel.mp hzero
      have hrootRead :
          AspisR1EmptyRootCandidate.pool_v1.pair_forest_semantic_terminal.empty_root level =
            .ok expected := by simpa [hzero] using htmp
      obtain ⟨root, hroot, hcanonical, hvalues⟩ :=
        AspisR1.EmptyRootBindingModel.source_root_canonical level (by omega)
      have hrootEq : expected = root := Result.ok.inj (hrootRead.symm.trans hroot)
      subst expected
      rw [if_pos (Or.inr hbitZero)]
      funext lane
      simp [AspisR1.SemanticPublicModel.digest,
        frozenEmptyModel, hvalues lane]
    · have hnotZero : bit ≠ 0#u64 := hzero
      have hnotBit : ¬ R0P.digestBitZero
          (AspisR1.SemanticPublicModel.exactPublic public1) ⟨level.val, hlevel⟩ := by
        intro hb
        exact hnotZero (hbitModel.mpr hb)
      have hread : Array.index_usize public1.transition.live_snapshot.frontier level =
          .ok expected := by simpa [hzero] using htmp
      have hbound : level.val < public1.transition.live_snapshot.frontier.length := by
        simpa [public1.transition.live_snapshot.frontier.property] using hlevel
      obtain ⟨q, hreadQ, hqvalue⟩ := WP.spec_imp_exists
        (Array.index_usize_spec public1.transition.live_snapshot.frontier level hbound)
      have hq : expected = q := Result.ok.inj (hread.symm.trans hreadQ)
      subst expected
      have hqvalue' : q = public1.transition.live_snapshot.frontier.val[level.val]'(by
          simpa [public1.transition.live_snapshot.frontier.property] using hlevel) := by
        simpa using hqvalue
      have hdisj : ¬ (level.val < carry.val ∨
          R0P.digestBitZero (AspisR1.SemanticPublicModel.exactPublic public1)
            ⟨level.val, hlevel⟩) := by
        intro h
        cases h with
        | inl hl => exact hlow hl
        | inr hb => exact hnotBit hb
      rw [if_neg hdisj]
      funext lane
      simp [AspisR1.SemanticPublicModel.digest,
        AspisR1.SemanticPublicModel.exactPublic, hqvalue']

#print axioms expectedAt_matches_noncarry_model
end RowMeaning
end AspisR1TerminalValidateTransitionCandidate
