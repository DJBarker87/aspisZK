import OccupancyGeneratedSlice
import SemanticPublicModel
import TerminalDigestBranchBits
import R0P.Digest

set_option autoImplicit false
namespace AspisR1TerminalDigestPublicLoop.BranchModel
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev U64 := UScalar UScalarTy.U64
abbrev Usize := UScalar UScalarTy.Usize

/-- The literal generated `next_pair_index >>> level` and `&&& 1` values
select precisely the retained exact-public frontier branch. -/
theorem live_snapshot_branch
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (level : Usize) (hlevel : level.val < 20) :
    ∃ shifted bit : U64,
      (public1.transition.live_snapshot.next_pair_index >>> level) = .ok shifted ∧
      lift (shifted &&& (1#u64)) = .ok bit ∧
      (bit = 0#u64 ↔ R0P.digestBitZero
        (AspisR1.SemanticPublicModel.exactPublic public1)
        ⟨level.val, hlevel⟩) := by
  have hlevel64 : level.val < UScalarTy.U64.numBits := by
    exact lt_of_lt_of_le hlevel (by decide)
  obtain ⟨shifted, hshift, _⟩ := WP.spec_imp_exists
    (UScalar.ShiftRight_spec public1.transition.live_snapshot.next_pair_index
      level hlevel64)
  obtain ⟨bit, hbit, _⟩ := WP.spec_imp_exists
    (UScalar.and_spec shifted (1#u64))
  refine ⟨shifted, bit, hshift, hbit, ?_⟩
  change bit = 0#u64 ↔
    ((public1.transition.live_snapshot.next_pair_index.val >>> level.val) &&& 1) = 0
  exact AspisR1TerminalDigestPublicLoop.BranchBits.shifted_low_bit_zero_iff
    public1.transition.live_snapshot.next_pair_index level hlevel64
    shifted hshift bit hbit

#print axioms live_snapshot_branch
end AspisR1TerminalDigestPublicLoop.BranchModel
