import AspisR1PublicPreparation.Funs
import ExtractedQM31SamplerCorrect

/-! Nominal transport to the existing proved sampler, not a second sampler
model. Numeric loop bodies are the identical extracted programs. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.SamplerTransport

abbrev OldQM := AspisR1Qm31SamplerIndex.field.QM31
abbrev NewQM := aspis_core.field.QM31

def toOld (q : NewQM) : OldQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

def fromOld (q : OldQM) : NewQM :=
  ⟨⟨q.c0.a, q.c0.b⟩, ⟨q.c1.a, q.c1.b⟩⟩

@[simp] theorem toOld_fromOld (q : OldQM) : toOld (fromOld q) = q := by cases q; rfl
@[simp] theorem fromOld_toOld (q : NewQM) : fromOld (toOld q) = q := by cases q; rfl

theorem div_pass_eq (rank : Array U32 8#usize) :
    sampler.qm31_div_pass rank = AspisR1Qm31SamplerIndex.sampler.qm31_div_pass rank := by
  simp only [sampler.qm31_div_pass, AspisR1Qm31SamplerIndex.sampler.qm31_div_pass,
    sampler.qm31_div_pass_loop, AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop,
    sampler.qm31_div_pass_loop.body, AspisR1Qm31SamplerIndex.sampler.qm31_div_pass_loop.body,
    aspis_core.field.P, AspisR1Qm31SamplerIndex.field.P]

theorem digits_eq (block : Array U8 32#usize) :
    sampler.qm31_digits block = AspisR1Qm31SamplerIndex.sampler.qm31_digits block := by
  simp only [sampler.qm31_digits, AspisR1Qm31SamplerIndex.sampler.qm31_digits,
    sampler.qm31_digits_loop0, AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0,
    sampler.qm31_digits_loop0.body, AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop0.body,
    sampler.qm31_digits_loop1, AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1,
    sampler.qm31_digits_loop1.body, AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1.body,
    div_pass_eq]

private theorem bind_map {α β γ : Type} (m : Result α) (f : α → Result β) (g : β → γ) :
    (do let b ← (do let a ← m; f a); ok (g b)) =
      (do let a ← m; let b ← f a; ok (g b)) := by
  cases m <;> rfl

/-- The current nominal result is the same four machine coordinates as the
already proved index sampler, with all failure/divergence cases retained. -/
theorem sample_eq (block : Array U8 32#usize) :
    (do let q ← sampler.qm31_sample block; ok (toOld q)) =
      AspisR1Qm31SamplerIndex.sampler.qm31_sample block := by
  simp only [sampler.qm31_sample, AspisR1Qm31SamplerIndex.sampler.qm31_sample,
    aspis_core.field.CM31.new, AspisR1Qm31SamplerIndex.field.CM31.new,
    bind_tc_ok, bind_map, digits_eq]
  rfl

theorem sample_toOld_success (block : Array U8 32#usize) (q : NewQM)
    (h : sampler.qm31_sample block = ok q) :
    AspisR1Qm31SamplerIndex.sampler.qm31_sample block = ok (toOld q) := by
  rw [← sample_eq, h]
  rfl

/-- The accepted current-QM31 canonical carrier and existing byte-rank equation
are inherited from the already checked sampler, with no success premise. -/
theorem sample_total (block : Array U8 32#usize) :
    ∃ q : NewQM, sampler.qm31_sample block = ok q ∧
      AspisR1.ExtractedQM31SamplerCarrier.CurrentCanonicalQM
        (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (toOld q)) ∧
      AspisR1.ExtractedQM31SamplerCorrect.coordinates (toOld q) =
        AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) := by
  obtain ⟨old, hold, hc, hv⟩ := AspisR1.ExtractedQM31SamplerCorrect.sample_total block
  have hm : (do let q ← sampler.qm31_sample block; ok (toOld q)) = ok old :=
    (sample_eq block).trans hold
  cases hn : sampler.qm31_sample block with
  | ok q =>
    rw [hn, bind_tc_ok] at hm
    have he : toOld q = old := Result.ok.inj hm
    exact ⟨q, rfl, he ▸ hc, he ▸ hv⟩
  | fail e => simp only [hn, bind_tc_fail] at hm; cases hm
  | div => simp only [hn, bind_tc_div] at hm; cases hm

theorem sample_coordinates_of_success (block : Array U8 32#usize) (q : NewQM)
    (h : sampler.qm31_sample block = ok q) :
    AspisR1.ExtractedQM31SamplerCorrect.coordinates (toOld q) =
      AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) :=
  AspisR1.ExtractedQM31SamplerCorrect.sample_coordinates_of_success block (toOld q)
    (sample_toOld_success block q h)

/-- Reuses the accepted current-QM31 decoder equality, discharging canonicality
from these actual sampled outputs and transporting only the nominal carrier. -/
theorem sampled_decode_eq_iff (b1 b2 : Array U8 32#usize) (q1 q2 : NewQM)
    (h1 : sampler.qm31_sample b1 = ok q1) (h2 : sampler.qm31_sample b2 = ok q2) :
    AspisR1.ExtractedCurrentQM31Exact.decode
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (toOld q1)) =
      AspisR1.ExtractedCurrentQM31Exact.decode
      (AspisR1.ExtractedQM31SamplerCarrier.toCurrent (toOld q2)) ↔ q1 = q2 := by
  rw [AspisR1.ExtractedQM31SamplerCorrect.sampled_decode_eq_iff b1 b2 (toOld q1) (toOld q2)
    (sample_toOld_success b1 q1 h1) (sample_toOld_success b2 q2 h2)]
  constructor
  · intro he
    simpa only [fromOld_toOld] using congrArg fromOld he
  · exact congrArg toOld

#print axioms toOld_fromOld
#print axioms fromOld_toOld
#print axioms div_pass_eq
#print axioms digits_eq
#print axioms sample_eq
#print axioms sample_toOld_success
#print axioms sample_total
#print axioms sample_coordinates_of_success
#print axioms sampled_decode_eq_iff
end AspisR1PublicPreparation.SamplerTransport
