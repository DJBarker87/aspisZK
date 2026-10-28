import R1Z.ProverRwSamplerTransport

/-! Total selected QM31 sampler correspondence to the existing byte-rank model.
No desired sampler equality, success, or canonicality premise is assumed. -/
set_option autoImplicit false
namespace R1Z.ProverRwSamplerModel
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedQM31SamplerCarrier
open ProverRwSamplerTransport
abbrev NewQM := ProverRwSampler.aspis_core.field.QM31

def fromOld (q : SamplerQM) : NewQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toOld (q : NewQM) : SamplerQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem toOld_fromOld (q : SamplerQM) : toOld (fromOld q) = q := by
  cases q with
  | mk a b => cases a; cases b; rfl

theorem index_four (ds : Digits) (i : Usize) (hi : i.val < 4) :
    Array.index_usize ds i = ok (digit ds ⟨i.val,hi⟩) := by
  have hb : i.val < ds.length := by
    have := ds.property
    change ds.val.length = 4 at this
    change i.val < ds.val.length
    omega
  obtain ⟨x,hx,hv⟩ := WP.spec_imp_exists (Array.index_usize_spec ds i hb)
  simpa only [digit] using hx.trans (congrArg Result.ok hv)

theorem sample_of_digits (block : Array U8 32#usize) (ds : Digits)
    (h : ProverRwSampler.sampler.qm31_digits block = ok ds) :
    ProverRwSampler.sampler.qm31_sample block = ok (fromOld (packed ds)) := by
  have h0 := index_four ds 0#usize (by decide)
  have h1 := index_four ds 1#usize (by decide)
  have h2 := index_four ds 2#usize (by decide)
  have h3 := index_four ds 3#usize (by decide)
  have e0 : (⟨(0#usize).val, by decide⟩ : Fin 4) = 0 := by decide
  have e1 : (⟨(1#usize).val, by decide⟩ : Fin 4) = 1 := by decide
  have e2 : (⟨(2#usize).val, by decide⟩ : Fin 4) = 2 := by decide
  have e3 : (⟨(3#usize).val, by decide⟩ : Fin 4) = 3 := by decide
  simp only [ProverRwSampler.sampler.qm31_sample,h,bind_tc_ok,h0,h1,h2,h3,
    e0,e1,e2,e3,ProverRwSampler.aspis_core.field.CM31.new,packed,fromOld]

theorem sample_exact (block : Array U8 32#usize) :
    ProverRwSampler.sampler.qm31_sample block = (do
      let q ← AspisR1Qm31SamplerIndex.sampler.qm31_sample block
      ok (fromOld q)) := by
  obtain ⟨ds,hd,_,_⟩ := AspisR1.ExtractedQM31SamplerDigits.digits_total block
  have hn : ProverRwSampler.sampler.qm31_digits block = ok ds :=
    (digits_exact block).trans hd
  rw [sample_of_digits block ds hn, qm31_sample_of_digits block ds hd]
  rfl

/-- Reuse the established source byte-rank theorem for the selected release
lowering. All four canonical coordinates and total success are conclusions. -/
theorem sample_total (block : Array U8 32#usize) :
    ∃ q : NewQM,
      ProverRwSampler.sampler.qm31_sample block = ok q ∧
      CurrentCanonicalQM (toCurrent (toOld q)) ∧
      AspisR1.ExtractedQM31SamplerCorrect.coordinates (toOld q) =
        AspisR1.SamplerNatModel.qm31Digits (AspisR1.SourceSamplerByteRank.rank block) := by
  obtain ⟨q,hq,hc,hv⟩ := AspisR1.ExtractedQM31SamplerCorrect.sample_total block
  refine ⟨fromOld q, ?_, ?_, ?_⟩
  · rw [sample_exact,hq]
    rfl
  · simpa only [toOld_fromOld] using hc
  · simpa only [toOld_fromOld] using hv

#print axioms toOld_fromOld
#print axioms index_four
#print axioms sample_of_digits
#print axioms sample_exact
#print axioms sample_total
end R1Z.ProverRwSamplerModel
