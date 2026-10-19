import AspisR1RhoScalarK.Funs
import CuSavingsRhoDiagnostics
import CuSavingsRhoInitRow
import ExtractedQM31SamplerDigits

/-! Canonicality follows from the actual unchanged scalar_k caller and the
already checked exact sampler. No successful block/sampler premise is assumed.
The outcome equation retains all shared block failures and divergence.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoScalarK
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow

private theorem bind_ok {A B : Type} (m : Result A) (f : A → Result B) (out : B)
    (h : (do let x ← m;f x) = .ok out) :
    ∃ x,m = .ok x ∧ f x = .ok out := by
  cases m with
  | fail error => cases h
  | div => cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem sampler_total (block : Array U8 32#usize) :
    ∃ q : field.QM31,sampler.qm31_sample block = .ok q ∧ Canonical q := by
  obtain ⟨digits,hd,_,hc⟩ := ExtractedQM31SamplerDigits.digits_total block
  let packed : AspisR1Qm31SamplerIndex.field.QM31 :=
    ⟨⟨CuSavingsRhoValue.wordAt digits 0,CuSavingsRhoValue.wordAt digits 1⟩,
      ⟨CuSavingsRhoValue.wordAt digits 2,CuSavingsRhoValue.wordAt digits 3⟩⟩
  have h0 := CuSavingsRhoValue.array_read digits 0#usize (by scalar_tac)
  have h1 := CuSavingsRhoValue.array_read digits 1#usize (by scalar_tac)
  have h2 := CuSavingsRhoValue.array_read digits 2#usize (by scalar_tac)
  have h3 := CuSavingsRhoValue.array_read digits 3#usize (by scalar_tac)
  have e0 : (⟨(0#usize).val,by scalar_tac⟩ : Fin 4)=0 := by decide
  have e1 : (⟨(1#usize).val,by scalar_tac⟩ : Fin 4)=1 := by decide
  have e2 : (⟨(2#usize).val,by scalar_tac⟩ : Fin 4)=2 := by decide
  have e3 : (⟨(3#usize).val,by scalar_tac⟩ : Fin 4)=3 := by decide
  have hs : AspisR1Qm31SamplerIndex.sampler.qm31_sample block = .ok packed := by
    simp only [AspisR1Qm31SamplerIndex.sampler.qm31_sample,hd,bind_tc_ok,h0,h1,h2,h3,
      AspisR1Qm31SamplerIndex.field.CM31.new,e0,e1,e2,e3,packed]
  refine ⟨sampler.fromSource packed,?_,?_⟩
  · simp only [sampler.qm31_sample,hs,bind_tc_ok]
  · have bound (j : Fin 4) : (CuSavingsRhoValue.wordAt digits j).val < AspisV8R17.RawReducer.P := by
      exact hc _ (List.getElem_mem _)
    intro j
    fin_cases j
    · exact bound 0
    · exact bound 1
    · exact bound 2
    · exact bound 3

theorem sampler_success (block : Array U8 32#usize) (q : field.QM31)
    (h : sampler.qm31_sample block = .ok q) : Canonical q := by
  obtain ⟨out,hs,hc⟩ := sampler_total block
  have heq := Result.ok.inj (h.symm.trans hs)
  exact heq.symm ▸ hc

variable [ScalarKBlocks]

theorem source_outcome {H : Type} (D : Digest32 H) (self : transcript.Transcript H)
    (row : U8) (payload : Slice U8) :
    transcript.Transcript.scalar_k D self row payload = (do
      let (block,after) ← transcript.Transcript.block D self row payload
      let q ← sampler.qm31_sample block
      .ok (q,after)) := by
  unfold transcript.Transcript.scalar_k
  cases hb : transcript.Transcript.block D self row payload with
  | fail error => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨block,after⟩
    simp only [bind_tc_ok,uncurry_apply_pair]
    cases hs : sampler.qm31_sample block with
    | fail error => rfl
    | div => rfl
    | ok q =>
      obtain ⟨wide,hw⟩ := CuSavingsRhoDiagnostics.from_qm31_total q
      simp only [bind_tc_ok,lift,hw,trace.value]

theorem source_success {H : Type} (D : Digest32 H) (self after : transcript.Transcript H)
    (row : U8) (payload : Slice U8) (q : field.QM31)
    (h : transcript.Transcript.scalar_k D self row payload = .ok (q,after)) :
    Canonical q ∧ ∃ block,
      transcript.Transcript.block D self row payload = .ok (block,after) ∧
      sampler.qm31_sample block = .ok q := by
  rw [source_outcome] at h
  obtain ⟨pair,hblock,h⟩ := bind_ok _ _ _ h
  rcases pair with ⟨block,mid⟩
  simp only [uncurry_apply_pair] at h
  obtain ⟨value,hs,h⟩ := bind_ok _ _ _ h
  have hc := sampler_success block value hs
  have heq := Result.ok.inj h
  have hv := congrArg Prod.fst heq
  have ht := congrArg Prod.snd heq
  change value=q at hv
  change mid=after at ht
  refine ⟨by simpa only [hv] using hc,block,?_,?_⟩
  · simpa only [ht] using hblock
  · simpa only [hv] using hs

#print axioms sampler_total
#print axioms sampler_success
#print axioms source_outcome
#print axioms source_success
end AspisR1.CuSavingsRhoScalarK
