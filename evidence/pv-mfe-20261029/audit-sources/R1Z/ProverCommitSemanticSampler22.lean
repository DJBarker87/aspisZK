import ExtractedDigest32SamplerTransport
import AspisV8R19.SqueezeOracleBridge
import R0P.SemD2

/-! Fixed source sampler to the existing selected semantic challenge. This
uses the already checked current-QM31 equality/decoder and fixed algebraMap;
no new field, sampler, embedding parameter or success premise is introduced. -/
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace R1Z.ProverCommitSemanticSampler22
open AspisR1 AspisR1PublicPreparation AspisV8R15.ExactTowerBase
open AspisV8R19.R599CanonicalFieldTuple
open AspisV8R19.SqueezeOracleBridge
open SamplerMachineBounds

theorem field_pos : 0 < AspisV8R15.ExactTowerBase.P := by decide

/-- The same four low digits in the retained positional equivalence. -/
theorem digits_as_tuple (x : Nat) :
    SamplerNatModel.qm31Digits x =
      (List.ofFn (SamplerRanking.canonicalDigits AspisV8R15.ExactTowerBase.P 4 x field_pos)).map Fin.val := by
  rw [ofFn_four_values]
  simp [SamplerNatModel.qm31Digits, SamplerNatModel.lowDigits,
    SamplerRanking.canonicalDigits, SamplerMachineBounds.P, AspisV8R15.ExactTowerBase.P, Nat.div_div_eq_div_mul, pow_succ]

theorem model_qm31 (block : Array U8 32#usize) :
    AspisV8R19.SamplerFieldDecode.decode
      (SamplerNatModel.qm31Digits (SourceSamplerByteRank.rank block)) =
      R0P.SemSource.qm31Sample (decodeState block) := by
  rw [digits_as_tuple, listDecode_tuple]
  change tupleFieldEquiv
      (SamplerRanking.canonicalDigits AspisV8R15.ExactTowerBase.P 4 (SourceSamplerByteRank.rank block) field_pos) =
    tupleFieldEquiv _
  apply congrArg tupleFieldEquiv
  rw [SamplerRanking.canonicalDigits_eq_rank_symm]
  rfl

/-- Exact current decoder of the actual sampled machine result. The only
success input is the actual source sampler call; its model law is concluded. -/
theorem sample_qm31 (block : Array U8 32#usize) (q : aspis_core.field.QM31)
    (h : sampler.qm31_sample block = ok q) :
    ExtractedCurrentQM31Exact.decode
      (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld q)) =
      R0P.SemSource.qm31Sample (decodeState block) := by
  calc
    _ = AspisV8R19.SamplerFieldDecode.decode
        (ExtractedQM31SamplerCorrect.coordinates (SamplerTransport.toOld q)) := rfl
    _ = AspisV8R19.SamplerFieldDecode.decode
        (SamplerNatModel.qm31Digits (SourceSamplerByteRank.rank block)) :=
      congrArg AspisV8R19.SamplerFieldDecode.decode
        (SamplerTransport.sample_coordinates_of_success block q h)
    _ = _ := model_qm31 block

/-- The fixed exact-tower embedding agrees with the selected semantic
challenge on the exact source read1 block. -/
theorem sample_semChal (block : Array U8 32#usize) (q : aspis_core.field.QM31)
    (h : sampler.qm31_sample block = ok q) :
    algebraMap QM31Exact AspisWideTower.WideExact
      (ExtractedCurrentQM31Exact.decode
        (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld q))) =
      R0P.SemSource.semChal (decodeState block) :=
  congrArg (algebraMap QM31Exact AspisWideTower.WideExact) (sample_qm31 block q h)

/-- The actual extracted sampler supplies its successful result; there is
no caller-provided sampling-success premise in this statement. -/
theorem sample_total_semChal (block : Array U8 32#usize) :
    ∃ q : aspis_core.field.QM31, sampler.qm31_sample block = ok q ∧
      algebraMap QM31Exact AspisWideTower.WideExact
        (ExtractedCurrentQM31Exact.decode
          (ExtractedQM31SamplerCarrier.toCurrent (SamplerTransport.toOld q))) =
        R0P.SemSource.semChal (decodeState block) := by
  obtain ⟨q,hq,_,_⟩ := SamplerTransport.sample_total block
  exact ⟨q,hq,sample_semChal block q hq⟩

#print axioms field_pos
#print axioms sample_total_semChal
#print axioms digits_as_tuple
#print axioms model_qm31
#print axioms sample_qm31
#print axioms sample_semChal
end R1Z.ProverCommitSemanticSampler22
end
