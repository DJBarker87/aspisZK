import AspisR1Post25Sampler.Funs
import R0C.ModuloField
import R1SamplerNatModel
import R1SamplerRanking
import IndexedCandidateOrdinarySampleBridgeV3
import IndexedCandidateDecode8RetainedBridgeV3

/-! Candidate-only composition of the extracted ordinary sampler with the
retained eight-limb field ranking. This does not claim production equivalence. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV3

open Aeneas Aeneas.Std Result
open AspisR1Post25Sampler
open AspisR1.SourceSamplerByteRank
open AspisR1.SamplerMachineBounds
open AspisR1.SamplerNatModel
open AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3

private def digitAt (digits : Array U32 8#usize) (i : Fin 8) : Nat :=
  (digits.val[i.val]'(by simpa [digits.property] using i.isLt)).val

private theorem lowDigits_getElem {p n x i : Nat} (hi : i < n) :
    (SamplerNatModel.lowDigits p n x)[i]'(by
      rw [SamplerNatModel.lowDigits_length]
      exact hi) = x / p ^ i % p := by
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
          simp [Nat.mul_comm]

private theorem values_getD (digits : Array U32 8#usize) (i : Fin 8) :
    (AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values digits).getD i.val 0 =
      digitAt digits i := by
  rw [List.getD_eq_getElem _ _ (by
    rw [AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values_length]
    exact i.isLt)]
  simp [AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values, digitAt]

private theorem ordinaryDigits_getD (rankValue : Nat) (i : Fin 8) :
    (ordinaryDigits rankValue).getD i.val 0 = rankValue / P ^ i.val % P := by
  rw [List.getD_eq_getElem _ _ (by
    rw [ordinaryDigits, SamplerNatModel.lowDigits_length]
    exact i.isLt)]
  rw [ordinaryDigits, lowDigits_getElem i.isLt]

private theorem retained_eq_canonical (digits : Array U32 8#usize)
    (hcanonical : ∀ i : Fin 8, digitAt digits i < P)
    (rankValue : Nat)
    (hrank : ∀ i : Fin 8, digitAt digits i = rankValue / P ^ i.val % P) :
    retainedDigits digits (by intro i; exact hcanonical i) =
      SamplerRanking.canonicalDigits P 8 rankValue P_pos := by
  funext i
  apply Fin.ext
  simp only [retainedDigits, SamplerRanking.canonicalDigits]
  rw [hrank]

private theorem pow8_pos : 0 < P ^ 8 := Nat.pow_pos P_pos

/-- The fresh candidate `ordinary_sample` owner returns exactly the retained
base-P rank of the byte block reduced modulo P^8. -/
theorem ordinary_sample_candidate_eq_fieldRank (block : Array U8 32#usize) :
    ∃ value : CandidateWide,
      sampler.ordinary_sample block = .ok value ∧
      candidateWideToExact value =
        R0C.ModuloField.fieldRank ⟨rank block % P ^ 8, Nat.mod_lt _ pow8_pos⟩ := by
  obtain ⟨_outRank, digits, _highWord, _hlow, hordinary, hvalues, _hpos, _hquot⟩ :=
    AspisR1.ExtractedQM31SamplerIndexedOrdinaryBridgeV1.ordinary_sample_candidate block
  have hcanonical : ∀ i : Fin 8, digitAt digits i < P := by
    intro i
    calc
      digitAt digits i =
          (AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values digits).getD i.val 0 :=
            (values_getD digits i).symm
      _ = (ordinaryDigits (rank block)).getD i.val 0 :=
            congrArg (fun xs : List Nat => xs.getD i.val 0) hvalues
      _ = rank block / P ^ i.val % P := ordinaryDigits_getD (rank block) i
      _ < P := Nat.mod_lt _ P_pos
  have hrank : ∀ i : Fin 8,
      digitAt digits i = rank block / P ^ i.val % P := by
    intro i
    calc
      digitAt digits i =
          (AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values digits).getD i.val 0 :=
            (values_getD digits i).symm
      _ = (ordinaryDigits (rank block)).getD i.val 0 :=
            congrArg (fun xs : List Nat => xs.getD i.val 0) hvalues
      _ = rank block / P ^ i.val % P := ordinaryDigits_getD (rank block) i
  have hcanonicalDigits := retained_eq_canonical digits hcanonical (rank block) hrank
  obtain ⟨value, hdecode, hretained⟩ := decode8_candidate_eq_retained digits hcanonical
  have hfield :
      R0C.ModuloField.fieldRank ⟨rank block % P ^ 8, Nat.mod_lt _ pow8_pos⟩ =
        R0C.ModuloField.digitsField
          (SamplerRanking.canonicalDigits P 8 (rank block) P_pos) := by
    rw [R0C.ModuloField.fieldRank, Equiv.trans_apply]
    rw [← SamplerRanking.canonicalDigits_eq_rank_symm P_pos]
    rfl
  refine ⟨value, ?_, ?_⟩
  · rw [hordinary, hdecode]
  · rw [hretained, hcanonicalDigits, hfield]

#print axioms ordinary_sample_candidate_eq_fieldRank

end AspisR1.ExtractedQM31SamplerIndexedOrdinaryRetainedBridgeV3
