import ExtractedQM31SamplerDivision
import R4TransportWideReference

/-! Eight applications of the actual extracted owned-array pass. The optimized
Rust iterator shell is bound separately by the source step packet. -/
set_option autoImplicit false
namespace AspisR1.R4Transport2WideReference
open Aeneas Aeneas.Std Result
open AspisR1Qm31SamplerIndex
open ExtractedQM31SamplerPassLoop SamplerWordPass

/-- Reference uses the extracted source pass, not a supplied division oracle. -/
def extractedRun : Nat → Array U32 8#usize → Result (List Nat × Array U32 8#usize)
  | 0, rank => ok ([], rank)
  | n+1, rank => do
    let pass ← sampler.qm31_div_pass rank
    let tail ← extractedRun n pass.1
    ok (pass.2.val :: tail.1, tail.2)

theorem extractedRun_correct (n : Nat) (rank : Array U32 8#usize) :
    ∃ ds out, extractedRun n rank = ok (ds, out) ∧
      ds = (SamplerRepeatedPass.run n (words rank).reverse).1 ∧
      (words out).reverse = (SamplerRepeatedPass.run n (words rank).reverse).2 := by
  induction n generalizing rank with
  | zero => exact ⟨[], rank, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨q, d, hpass, hq, hd, _⟩ :=
      ExtractedQM31SamplerDivision.div_pass_correct rank
    obtain ⟨ds, out, hexec, hds, hout⟩ := ih q
    refine ⟨d.val :: ds, out, ?_, ?_, ?_⟩
    · simp only [extractedRun, hpass, bind_tc_ok, hexec]
    · simp only [SamplerRepeatedPass.run]
      rw [hd, hds, hq]
    · simp only [SamplerRepeatedPass.run]
      rw [hout, hq]

theorem extractedRun_values (n : Nat) (rank : Array U32 8#usize) :
    ∃ ds out, extractedRun n rank = ok (ds, out) ∧
      ds = SamplerNatModel.lowDigits SamplerMachineBounds.P n
        (SamplerRepeatedPass.wordValue (words rank).reverse) ∧
      SamplerRepeatedPass.wordValue (words out).reverse =
        SamplerRepeatedPass.wordValue (words rank).reverse / SamplerMachineBounds.P^n := by
  obtain ⟨ds, out, hexec, hds, hout⟩ := extractedRun_correct n rank
  refine ⟨ds, out, hexec, ?_, ?_⟩
  · rw [hds, SamplerRepeatedPass.run_digits]
  · rw [hout, SamplerRepeatedPass.run_remaining]

/-- Instantiating the byte-read array suffices; no success premise on the pass. -/
theorem eight_passes_byte_model (block : Array U8 32#usize)
    (rank : Array U32 8#usize)
    (hbytes : (words rank).reverse = SamplerBytePass.digits block) :
    ∃ ds out, extractedRun 8 rank = ok (ds, out) ∧
      ds = SamplerNatModel.ordinaryDigits (SourceSamplerByteRank.rank block) ∧
      SamplerRepeatedPass.wordValue (words out).reverse =
        SourceSamplerByteRank.rank block / SamplerMachineBounds.P^8 := by
  obtain ⟨ds, out, hexec, hds, hout⟩ := extractedRun_values 8 rank
  refine ⟨ds, out, hexec, ?_, ?_⟩
  · simpa only [hbytes, SourceSamplerByteRank.word_value,
      SamplerNatModel.ordinaryDigits] using hds
  · simpa only [hbytes, SourceSamplerByteRank.word_value] using hout

#print axioms extractedRun_correct
#print axioms extractedRun_values
#print axioms eight_passes_byte_model
end AspisR1.R4Transport2WideReference
