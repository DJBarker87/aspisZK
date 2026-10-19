import ExtractedQM31SamplerDigits
import ExtractedQM31SamplerCarrier
import R1SourceSamplerByteRank

/-! Exact emitted sampler correspondence with the existing byte-rank model.
No transcript/caller timing or source-to-binary assertion is included. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerCorrect
open Aeneas Aeneas.Std Result
open AspisR1Qm31SamplerIndex
open SamplerMachineBounds SamplerRepeatedPass
open ExtractedQM31SamplerPassLoop ExtractedQM31SamplerBytes
open ExtractedQM31SamplerDigits ExtractedQM31SamplerCarrier

theorem byteWord_eq_four (block : Array U8 32#usize) (j : Fin 8) :
    byteWord block j = core.num.U32.from_le_bytes
      (AspisV8R19.SamplerWordRead.four block (4*j.val) (by omega)) := by
  unfold byteWord
  apply congrArg core.num.U32.from_le_bytes
  apply Subtype.ext
  change [byteAt block ⟨4*j.val, _⟩, byteAt block ⟨4*j.val+1, _⟩,
    byteAt block ⟨4*j.val+2, _⟩, byteAt block ⟨4*j.val+3, _⟩] =
    (block.val.drop (4*j.val)).take 4
  have hb : block.val.length = 32 := block.property
  have hlen : ((block.val.drop (4*j.val)).take 4).length = 4 := by
    simp only [List.length_take, List.length_drop, hb]
    omega
  rw [List.eq_getElem_of_length_eq_four _ hlen]
  simp only [byteAt, List.getElem_take, List.getElem_drop, Nat.add_zero]

theorem source_words_eq_model (block : Array U8 32#usize) :
    (words (byteWords block)).reverse = SamplerBytePass.digits block := by
  have h : (fun j : Fin 8 => decode32 (byteWord block j)) =
      (fun j : Fin 8 => UInt32.ofNat ((core.num.U32.from_le_bytes
        (AspisV8R19.SamplerWordRead.four block (4*j.val) (by omega))).val)) := by
    funext j
    exact congrArg (fun x : U32 => UInt32.ofNat x.val) (byteWord_eq_four block j)
  simpa only [words, byteWords, List.map_ofFn, SamplerBytePass.digits] using
    congrArg (fun f : Fin 8 → UInt32 => (List.ofFn f).reverse) h

/-- Actual machine-field projection in c0.a, c0.b, c1.a, c1.b order. -/
def coordinates (q : SamplerQM) : List Nat :=
  [q.c0.a.val, q.c0.b.val, q.c1.a.val, q.c1.b.val]

theorem packed_coordinates (ds : Digits) : coordinates (packed ds) = values ds := by
  have hlen : ds.val.length = 4 := ds.property
  have e0 : (0 : Fin 4).val = 0 := by decide
  have e1 : (1 : Fin 4).val = 1 := by decide
  have e2 : (2 : Fin 4).val = 2 := by decide
  have e3 : (3 : Fin 4).val = 3 := by decide
  have h := congrArg (List.map (fun d : U32 => d.val))
    (List.eq_getElem_of_length_eq_four ds.val hlen)
  simpa only [coordinates, packed, digit, values, e0, e1, e2, e3,
    List.map_cons, List.map_nil] using h.symm

/-- Unconditional totality, canonical current-carrier output, and the exact
existing rank model. Neither success nor a model equation is a premise. -/
theorem sample_total (block : Array U8 32#usize) :
    ∃ q : SamplerQM,
      sampler.qm31_sample block = ok q ∧
      CurrentCanonicalQM (toCurrent q) ∧
      coordinates q = SamplerNatModel.qm31Digits (SourceSamplerByteRank.rank block) := by
  obtain ⟨ds, hs, hv, hc⟩ := digits_total block
  have hcanonical : DigitsCanonical ds := by
    intro i
    have hmem : digit ds i ∈ ds.val := List.getElem_mem _
    have hd := hc (digit ds i) hmem
    simpa only [show P = 2147483647 from by norm_num [P]] using hd
  refine ⟨packed ds, qm31_sample_of_digits block ds hs,
    packed_current_canonical ds hcanonical, ?_⟩
  rw [packed_coordinates, hv, source_words_eq_model, SourceSamplerByteRank.word_value]

theorem sample_coordinates_of_success (block : Array U8 32#usize) (q : SamplerQM)
    (h : sampler.qm31_sample block = ok q) :
    coordinates q = SamplerNatModel.qm31Digits (SourceSamplerByteRank.rank block) := by
  obtain ⟨q0, h0, _, hv⟩ := sample_total block
  have heq : q = q0 := Result.ok.inj (h.symm.trans h0)
  rw [heq]
  exact hv

theorem sample_canonical_of_success (block : Array U8 32#usize) (q : SamplerQM)
    (h : sampler.qm31_sample block = ok q) : CurrentCanonicalQM (toCurrent q) := by
  obtain ⟨q0, h0, hc, _⟩ := sample_total block
  have heq : q = q0 := Result.ok.inj (h.symm.trans h0)
  rw [heq]
  exact hc

/-- The existing current-QM31 equality bridge now has its canonicality premises
discharged for both actual sampler outputs. -/
theorem sampled_decode_eq_iff (b1 b2 : Array U8 32#usize) (q1 q2 : SamplerQM)
    (h1 : sampler.qm31_sample b1 = ok q1)
    (h2 : sampler.qm31_sample b2 = ok q2) :
    ExtractedCurrentQM31Exact.decode (toCurrent q1) =
      ExtractedCurrentQM31Exact.decode (toCurrent q2) ↔ q1 = q2 :=
  decode_toCurrent_eq_iff q1 q2
    (sample_canonical_of_success b1 q1 h1) (sample_canonical_of_success b2 q2 h2)

#print axioms byteWord_eq_four
#print axioms source_words_eq_model
#print axioms packed_coordinates
#print axioms sample_total
#print axioms sample_coordinates_of_success
#print axioms sample_canonical_of_success
#print axioms sampled_decode_eq_iff

end AspisR1.ExtractedQM31SamplerCorrect
