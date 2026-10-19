import AspisR1Post25Sampler.Funs
import R0C.ModuloField
import SamplerNatModel
import SamplerRanking
import IndexedCandidateOrdinarySampleBridgeV3
import IndexedCandidateDecode8RetainedBridgeV3

/-! Candidate-only composition of the extracted ordinary sampler with the
retained eight-limb field ranking. This does not claim production equivalence. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV1

open Aeneas Aeneas.Std Result
open AspisR1Post25Sampler
open AspisR1.SourceSamplerByteRank
open AspisR1.SamplerMachineBounds
open AspisR1.SamplerNatModel
open AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3

private theorem lowDigits_getElem {p n x i : Nat} (hi : i < n) :
    (SamplerNatModel.lowDigits p n x)[i]'(by rw [SamplerNatModel.lowDigits_length]; exact hi) =
      x / p ^ i % p := by
  induction n generalizing x i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [SamplerNatModel.lowDigits]
      | succ i =>
          simp only [SamplerNatModel.lowDigits, List.getElem_cons_succ]
          have hi' : i < n := by omega
          rw [ih (x := x / p) hi']
          rw [Nat.div_div_eq_div_mul, pow_succ]
          simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

private theorem pow8_pos : 0 < P ^ 8 := by
  exact Nat.pow_pos P_pos

private theorem retained_eq_canonical (digits : Array U32 8#usize)
    (hcanonical : ∀ i : Fin 8, (digitAt digits i).val < P)
    (hrank : ∀ i : Fin 8, (digitAt digits i).val = rankValue / P ^ i.val % P)
    (rankValue : Nat) :
    retainedDigits digits hcanonical =
      SamplerRanking.canonicalDigits P 8 rankValue P_pos := by
  funext i
  apply Fin.ext
  simp only [retainedDigits, SamplerRanking.canonicalDigits]
  rw [hrank]

/-- The fresh candidate `ordinary_sample` owner returns exactly the retained
base-P rank of the byte block reduced modulo P^8. -/
theorem ordinary_sample_candidate_eq_fieldRank (block : Array U8 32#usize) :
    ∃ value : CandidateWide,
      sampler.ordinary_sample block = .ok value ∧
      candidateWideToExact value =
        R0C.ModuloField.fieldRank ⟨rank block % P ^ 8, Nat.mod_lt _ pow8_pos⟩ := by
  obtain ⟨outRank, digits, highWord, hlow, hordinary, hvalues, _hpos, _hquot⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOrdinaryBridgeV1.ordinary_sample_candidate block
  have hlen : (AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values digits).length = 8 :=
    AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values_length digits
  have hcanonical : ∀ i : Fin 8, (digitAt digits i).val < P := by
    intro i
    have hget := congrArg (fun xs : List Nat => xs[i.val]'(by simpa [hlen])) hvalues
    have hmodel : (ordinaryDigits (rank block))[i.val]'(by
        rw [lowDigits_length]; exact i.isLt) < P := by
      rw [ordinaryDigits, lowDigits_getElem i.isLt]
      exact Nat.mod_lt _ P_pos
    simpa [AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values,
      AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.digitAt] using
      hget.trans hmodel
  have hdigit : ∀ i : Fin 8,
      (digitAt digits i).val = rank block / P ^ i.val % P := by
    intro i
    have hget := congrArg (fun xs : List Nat => xs[i.val]'(by simpa [hlen])) hvalues
    have hmodel : (ordinaryDigits (rank block))[i.val]'(by
        rw [ordinaryDigits, lowDigits_length]; exact i.isLt) =
        rank block / P ^ i.val % P := by
      rw [ordinaryDigits, lowDigits_getElem i.isLt]
    simpa [AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values,
      AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.digitAt] using
      hget.trans hmodel
  obtain ⟨value, hdecode, hretained⟩ :=
    decode8_candidate_eq_retained digits hcanonical
  have hcanonicalDigits := retained_eq_canonical digits hcanonical hdigit (rank block)
  have hrank :
      R0C.ModuloField.fieldRank ⟨rank block % P ^ 8, Nat.mod_lt _ pow8_pos⟩ =
        R0C.ModuloField.digitsField
          (SamplerRanking.canonicalDigits P 8 (rank block) P_pos) := by
    rw [R0C.ModuloField.fieldRank, Equiv.trans_apply]
    rw [← SamplerRanking.canonicalDigits_eq_rank_symm P_pos]
    rfl
  refine ⟨value, ?_, ?_⟩
  · rw [hordinary, hdecode]
  · rw [hretained, hcanonicalDigits, hrank]

#print axioms ordinary_sample_candidate_eq_fieldRank

end AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV1
