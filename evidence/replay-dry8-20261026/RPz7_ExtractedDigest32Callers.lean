import RPz7_ExtractedDigest32Transcript
/-! Success inversion for the actual semantic wrapper and the actual opening
constructor/absorb/block. No claim about Observer effects or the outer verifier
is made by these local equations. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.CallerStep
open r1_wire TranscriptStep

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem semantic_success {H : Type} (D : aspis_core.Digest32 H)
    (self after : SemanticTranscript H) (record : ValidatedRecord)
    (q : aspis_core.field.QM31)
    (h : SemanticTranscript.semantic_validated D self record = ok (.Ok q, after)) :
    record.row.val ≤ 24 ∧ ∃ block,
      SemanticTranscript.sample_block_validated D self record.row record.framed =
        ok (.Ok block, after) ∧ sampler.qm31_sample block = ok q := by
  simp only [SemanticTranscript.semantic_validated, ValidatedRecord.impl.row,
    ValidatedRecord.impl.framed, bind_tc_ok] at h
  split at h
  · cases h
  · rename_i hadmit
    obtain ⟨⟨r, mid⟩, hs, h⟩ := bind_success _ _ _ h
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
    | Ok block =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      change (do
        let value ← sampler.qm31_sample block
        ok ((core.result.Result.Ok value : core.result.Result aspis_core.field.QM31 r1_wire.Error), mid)) =
        ok (core.result.Result.Ok q, after) at h
      obtain ⟨value, hv, h⟩ := bind_success _ _ _ h
      have hp := Result.ok.inj h
      have hq : value = q := core.result.Result.Ok.inj (congrArg Prod.fst hp)
      have ht : mid = after := congrArg Prod.snd hp
      refine ⟨by scalar_tac, block, ?_, ?_⟩
      · simpa only [ht] using hs
      · simpa only [hq] using hv

/-- The row bound, sampler success and three exact Digest32 calls follow from
actual semantic_validated success. The existing row-step proof supplies carry. -/
theorem semantic_step_success {H : Type} (D : aspis_core.Digest32 H)
    (self after : SemanticTranscript H) (record : ValidatedRecord)
    (q : aspis_core.field.QM31)
    (h : SemanticTranscript.semantic_validated D self record = ok (.Ok q, after)) :
    record.row = self.next_row ∧ ∃ block tag next absorbed state,
      tag.val = 160 + record.row.val ∧ next.val = record.row.val + 1 ∧
      D.digest self.hash (absorbParts self.state tag record.framed) = ok absorbed ∧
      D.digest self.hash (readParts absorbed 1#u8) = ok block ∧
      D.digest self.hash (readParts absorbed 2#u8) = ok state ∧
      sampler.qm31_sample block = ok q ∧
      after = { self with state, next_row := next } := by
  obtain ⟨hadmit, block, hs, hq⟩ := semantic_success D self after record q h
  obtain ⟨hr, tag, next, absorbed, state, ht, hn, ha, hb, hc, he⟩ :=
    TranscriptStep.step_success D self after record.row record.framed block (by omega) hs
  exact ⟨hr, block, tag, next, absorbed, state, ht, hn, ha, hb, hc, hq, he⟩

def openingDomain : Slice U8 := Array.to_slice
  (Array.make 29#usize [85#u8,78#u8,80#u8,82#u8,79#u8,86#u8,69#u8,68#u8,
    58#u8,82#u8,49#u8,58#u8,80#u8,82#u8,73#u8,86#u8,65#u8,84#u8,69#u8,
    45#u8,83#u8,65#u8,76#u8,84#u8,69#u8,68#u8,58#u8,80#u8,51#u8])

def variantTag : transport.Variant → U8
  | .S1 => 1#u8 | .S2 => 2#u8 | .D => 3#u8

def reseedParts (semantic : Bytes32) (variant : transport.Variant) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize [openingDomain,
    Array.to_slice (Array.make 1#usize [variantTag variant]), Array.to_slice semantic])

theorem opening_new_eq {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (semantic : Bytes32) (variant : transport.Variant) :
    transcript.Transcript.new D hash semantic variant =
      (do let state ← D.digest hash (reseedParts semantic variant)
          ok { state, hash }) := by
  cases variant <;> simp only [transcript.Transcript.new, transport.Variant.tag,
    variantTag, openingDomain, reseedParts, lift, bind_tc_ok]

theorem opening_new_success {H : Type} (D : aspis_core.Digest32 H) (hash : H)
    (semantic : Bytes32) (variant : transport.Variant) (after : transcript.Transcript H)
    (h : transcript.Transcript.new D hash semantic variant = ok after) :
    ∃ state, D.digest hash (reseedParts semantic variant) = ok state ∧
      after = { state, hash } := by
  rw [opening_new_eq] at h
  obtain ⟨state, hs, h⟩ := bind_success _ _ _ h
  exact ⟨state, hs, (Result.ok.inj h).symm⟩

def openingAbsorbParts (state : Bytes32) (tag : U8) (length : U32)
    (payload : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 4#usize [Array.to_slice state,
    Array.to_slice (Array.make 2#usize [0#u8, tag]),
    Array.to_slice (core.num.U32.to_le_bytes length), payload])

theorem opening_absorb_eq {H : Type} (D : aspis_core.Digest32 H)
    (self : transcript.Transcript H) (row tag : U8) (payload : Slice U8)
    (length : U32) (htag : 160#u8 + row = ok tag)
    (hlen : UScalar.cast .U32 (Slice.len payload) = length) :
    transcript.Transcript.absorb D self row payload =
      (do let state ← D.digest self.hash (openingAbsorbParts self.state tag length payload)
          ok { self with state }) := by
  simp only [transcript.Transcript.absorb, htag, hlen, openingAbsorbParts,
    lift, bind_tc_ok]

theorem opening_block_success {H : Type} (D : aspis_core.Digest32 H)
    (self after : transcript.Transcript H) (row : U8) (payload : Slice U8)
    (block : Bytes32)
    (h : transcript.Transcript.block D self row payload = ok (block, after)) :
    ∃ absorbed state,
      transcript.Transcript.absorb D self row payload = ok absorbed ∧
      D.digest absorbed.hash (readParts absorbed.state 1#u8) = ok block ∧
      D.digest absorbed.hash (readParts absorbed.state 2#u8) = ok state ∧
      after = { absorbed with state } := by
  simp only [transcript.Transcript.block, lift, bind_tc_ok] at h
  obtain ⟨absorbed, ha, h⟩ := bind_success _ _ _ h
  obtain ⟨actual, hb, h⟩ := bind_success _ _ _ h
  obtain ⟨state, hs, h⟩ := bind_success _ _ _ h
  have hp := Result.ok.inj h
  have he : actual = block := congrArg Prod.fst hp
  have ht := congrArg Prod.snd hp
  refine ⟨absorbed, state, ha, ?_, ?_, ht.symm⟩
  · simpa only [readParts, he] using hb
  · simpa only [readParts] using hs

#print axioms semantic_success
#print axioms semantic_step_success
#print axioms opening_new_eq
#print axioms opening_new_success
#print axioms opening_absorb_eq
#print axioms opening_block_success
#print axioms r1_wire.begin
#print axioms r1_wire.SemanticTranscript.semantic_validated
#print axioms transcript.Transcript.new
#print axioms transcript.Transcript.absorb
#print axioms transcript.Transcript.block
end AspisR1PublicPreparation.CallerStep
