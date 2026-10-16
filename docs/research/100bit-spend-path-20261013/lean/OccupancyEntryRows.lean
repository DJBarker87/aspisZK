import OccupancyGeneratedSlice
import SelectorRowCall
import ExtractedMaskReducerOps
import ExtractedMaskQM31Exact

/-! The actual source row constants and generated selector rows consumed by
`add_occupancy_lanes`; this keeps the source row accesses explicit. -/
set_option autoImplicit false
namespace AspisR1.OccupancyEntryRows

open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SelectorRowCall
open AspisR1.SelectorExpansionCorrectness
open AspisR1.ExtractedMaskReducerOps
open AspisR1.ExtractedMaskQM31Exact

abbrev QM := field.QM31
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev CanonicalQM := AspisR1.SelectorAtPointModel.Canonical

def inputRow : Usize := 1017#usize
def outputRow : Usize := 1018#usize

private theorem smallUsize_bound (n : Nat) (hn : n < 2048) :
    n < 2 ^ UScalarTy.Usize.numBits := by
  rw [UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
  have hmax := Usize.cMax_bound_concrete.1
  omega

private theorem mul_63_16 : UScalar.mul 63#usize 16#usize = .ok 1008#usize := by
  have hb : 63 * 16 < 2 ^ UScalarTy.Usize.numBits := by
    apply smallUsize_bound
    norm_num
  obtain ⟨q, hrun, hval⟩ := tryMk_success (ty := .Usize) (63 * 16) hb
  have hq : q = (1008#usize) := by
    apply UScalar.eq_of_val_eq
    simpa using hval
  change UScalar.mul 63#usize 16#usize = .ok (1008#usize)
  calc
    UScalar.mul 63#usize 16#usize = .ok q := by
      simpa [UScalar.mul] using hrun
    _ = .ok (1008#usize) := by rw [hq]

private theorem add_1008_9 : UScalar.add 1008#usize 9#usize = .ok 1017#usize := by
  have hb : 1008 + 9 < 2 ^ UScalarTy.Usize.numBits := by
    apply smallUsize_bound
    norm_num
  obtain ⟨q, hrun, hval⟩ := tryMk_success (ty := .Usize) (1008 + 9) hb
  have hq : q = (1017#usize) := by
    apply UScalar.eq_of_val_eq
    simpa using hval
  change UScalar.add 1008#usize 9#usize = .ok (1017#usize)
  calc
    UScalar.add 1008#usize 9#usize = .ok q := by
      simpa [UScalar.add] using hrun
    _ = .ok (1017#usize) := by rw [hq]

private theorem add_1008_10 : UScalar.add 1008#usize 10#usize = .ok 1018#usize := by
  have hb : 1008 + 10 < 2 ^ UScalarTy.Usize.numBits := by
    apply smallUsize_bound
    norm_num
  obtain ⟨q, hrun, hval⟩ := tryMk_success (ty := .Usize) (1008 + 10) hb
  have hq : q = (1018#usize) := by
    apply UScalar.eq_of_val_eq
    simpa using hval
  change UScalar.add 1008#usize 10#usize = .ok (1018#usize)
  calc
    UScalar.add 1008#usize 10#usize = .ok q := by
      simpa [UScalar.add] using hrun
    _ = .ok (1018#usize) := by rw [hq]

theorem input_occupancy_row_success :
    pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW = .ok inputRow := by
  rw [pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW.eq_def]
  change (do
    let base ← UScalar.mul 63#usize 16#usize
    UScalar.add base 9#usize) = .ok inputRow
  rw [mul_63_16]
  simp only [bind_tc_ok, add_1008_9]
  rfl

theorem output_occupancy_row_success :
    pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW = .ok outputRow := by
  rw [pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW.eq_def]
  change (do
    let base ← UScalar.mul 63#usize 16#usize
    UScalar.add base 10#usize) = .ok outputRow
  rw [mul_63_16]
  simp only [bind_tc_ok, add_1008_10]
  rfl

theorem selector_rows_success
    (selectors : Selectors)
    (hhigh : canonicalArray selectors.high) (hlow : canonicalArray selectors.low) :
    ∃ input output : QM,
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors inputRow = .ok input ∧
      CanonicalQM input ∧
      AspisR1.ExtractedMaskQM31Exact.decode input = decodedArray selectors.high 63 * decodedArray selectors.low 9 ∧
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors outputRow = .ok output ∧
      CanonicalQM output ∧
      AspisR1.ExtractedMaskQM31Exact.decode output = decodedArray selectors.high 63 * decodedArray selectors.low 10 := by
  have hinval : inputRow.val = 1017 := by change 1017 = 1017; rfl
  have houtval : outputRow.val = 1018 := by change 1018 = 1018; rfl
  have hinputBound : inputRow.val < 1024 := by rw [hinval]; omega
  have houtputBound : outputRow.val < 1024 := by rw [houtval]; omega
  obtain ⟨input, hin, hincan, hindec⟩ :=
    row_success_of_canonical selectors inputRow hinputBound hhigh hlow
  obtain ⟨output, hout, houtcan, houtdec⟩ :=
    row_success_of_canonical selectors outputRow houtputBound hhigh hlow
  have hinputQuot : inputRow.val / 16 = 63 := by rw [hinval]
  have hinputRem : inputRow.val % 16 = 9 := by rw [hinval]
  have houtputQuot : outputRow.val / 16 = 63 := by rw [houtval]
  have houtputRem : outputRow.val % 16 = 10 := by rw [houtval]
  refine ⟨input, output, hin, hincan, ?_, hout, houtcan, ?_⟩
  · simpa [hinputQuot, hinputRem] using hindec
  · simpa [houtputQuot, houtputRem] using houtdec

#print axioms input_occupancy_row_success
#print axioms output_occupancy_row_success
#print axioms selector_rows_success
end AspisR1.OccupancyEntryRows
