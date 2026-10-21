import ExtractedQM31SamplerDivision
import R1SamplerRepeatedPass
import ExtractedQM31SamplerCorrect

/-! Candidate-only composition: the indexed eight-pass loop that replaces the
unsupported `iter_mut().rev()` lowering. This does not claim correspondence to
current production `low_base_p_digits`; it proves the helper-call algorithm. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerIndexedCandidate
open Aeneas Aeneas.Std Result
open AspisR1Qm31SamplerIndex
open AspisR1.ExtractedQM31SamplerPassLoop
open AspisR1.ExtractedQM31SamplerDivision
open AspisR1.SamplerRepeatedPass
open AspisR1.SamplerWordPass
open AspisR1.SamplerMachineBounds

abbrev Words := Array U32 8#usize

/-- A successful complete source pass with its returned quotient and digit. -/
theorem pass_exists (rank : Words) :
    ∃ step : Words × U32,
      sampler.qm31_div_pass rank = ok step ∧
      (words step.1).reverse = (machineProcess 0 (words rank).reverse).2 ∧
      step.2.val = (machineProcess 0 (words rank).reverse).1.toNat ∧
      step.2.val < P := by
  rcases div_pass_correct rank with ⟨q, d, hpass, hq, hd, hlt⟩
  exact ⟨(q, d), hpass, hq, hd, hlt⟩

noncomputable def chosenPass (rank : Words) : Words × U32 :=
  Classical.choose (pass_exists rank)

theorem chosenPass_spec (rank : Words) :
    sampler.qm31_div_pass rank = ok (chosenPass rank) ∧
      (words (chosenPass rank).1).reverse =
        (machineProcess 0 (words rank).reverse).2 ∧
      (chosenPass rank).2.val =
        (machineProcess 0 (words rank).reverse).1.toNat ∧
      (chosenPass rank).2.val < P :=
  Classical.choose_spec (pass_exists rank)

/-- The source-shaped indexed loop: one complete division helper per digit. -/
noncomputable def indexedPasses : Nat → Words → List Nat × Words
  | 0, rank => ([], rank)
  | n + 1, rank =>
      let step := chosenPass rank
      let tail := indexedPasses n step.1
      (step.2.val :: tail.1, tail.2)

theorem indexedPasses_matches (n : Nat) (rank : Words) :
    (indexedPasses n rank).1 = (run n (words rank).reverse).1 ∧
      (words (indexedPasses n rank).2).reverse =
        (run n (words rank).reverse).2 := by
  induction n generalizing rank with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      have hs := chosenPass_spec rank
      obtain ⟨hdigits, hremaining⟩ := ih (chosenPass rank).1
      constructor
      · change (chosenPass rank).2.val ::
          (indexedPasses n (chosenPass rank).1).1 = _
        rw [hdigits, hs.2.2.1, hs.2.1]
        simp [run]
      · change (words (indexedPasses n (chosenPass rank).1).2).reverse = _
        rw [hremaining, hs.2.1]
        simp [run]

/-- The eight helper calls implement the existing low-base-P digit model and
leave the exact quotient by P^8 in the high words. -/
theorem indexedPasses_eight_correct (rank : Words) :
    (indexedPasses 8 rank).1 =
        AspisR1.SamplerNatModel.lowDigits P 8
          (wordValue (words rank).reverse) ∧
      wordValue ((words (indexedPasses 8 rank).2).reverse) =
        wordValue (words rank).reverse / P^8 := by
  obtain ⟨hdigits, hremaining⟩ := indexedPasses_matches 8 rank
  constructor
  · rw [hdigits, run_digits]
  · rw [hremaining, run_remaining]

/-- Byte-block specialization: the eight indexed helper passes consume the
same little-endian word array as the existing source-shaped byte parser. -/
theorem indexedPasses_eight_bytes (block : Array U8 32#usize) :
    (indexedPasses 8 (AspisR1.ExtractedQM31SamplerBytes.byteWords block)).1 =
        AspisR1.SamplerNatModel.ordinaryDigits
          (AspisR1.SourceSamplerByteRank.rank block) ∧
      wordValue ((words (indexedPasses 8
        (AspisR1.ExtractedQM31SamplerBytes.byteWords block)).2).reverse) =
        AspisR1.SourceSamplerByteRank.rank block / P^8 := by
  have hwordValue :
      wordValue (words (AspisR1.ExtractedQM31SamplerBytes.byteWords block)).reverse =
        AspisR1.SourceSamplerByteRank.rank block := by
    rw [AspisR1.ExtractedQM31SamplerCorrect.source_words_eq_model]
    exact AspisR1.SourceSamplerByteRank.word_value block
  have h := indexedPasses_eight_correct
    (AspisR1.ExtractedQM31SamplerBytes.byteWords block)
  rw [hwordValue] at h
  simpa [AspisR1.SamplerNatModel.ordinaryDigits,
    AspisR1.SamplerNatModel.ordinaryDigits] using h

#print axioms pass_exists
#print axioms chosenPass_spec
#print axioms indexedPasses_matches
#print axioms indexedPasses_eight_correct
#print axioms indexedPasses_eight_bytes

end AspisR1.ExtractedQM31SamplerIndexedCandidate
