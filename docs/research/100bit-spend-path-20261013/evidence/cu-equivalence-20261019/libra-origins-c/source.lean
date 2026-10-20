import CuSavingsLibraCaller
import CuSavingsCanonicalSampler
import CuSavingsCanonicalReader
import CuSavingsCanonicalKReader
import SemanticCallSelectedCanonical
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraOrigins
open Aeneas Aeneas.Std Result CuSavingsLibraConcrete
abbrev SampleE := AspisR1CanonicalSampler.field.wide_exact.WideExact
abbrev ReaderE := AspisR1CanonicalReader.field.wide_exact.WideExact
abbrev ReaderK := AspisR1CanonicalKReader.field.QM31
abbrev PublicK := AspisR1PublicPreparation.aspis_core.field.QM31

def sampleToL (x : SampleE) : L.E :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def readerToL (x : ReaderE) : L.E := CuSavingsLibraCaller.fromInput (AspisR1CanonicalReader.toInput x)
def readerKToL (x : ReaderK) : L.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def publicKToL (x : PublicK) : L.K := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩

variable [AspisR1CanonicalSampler.Shared] [AspisR1CanonicalReader.Runtime]
  [AspisR1CanonicalKReader.Runtime]
inductive Alpha : L.E → Prop
  | sampled {H : Type} (digest : AspisR1CanonicalSampler.Digest32 H)
      (self after : AspisR1CanonicalSampler.transcript.Transcript H)
      (row : U8) (payload : Slice U8) (value : SampleE)
      (h : AspisR1CanonicalSampler.transcript.Transcript.scalar digest self row payload false=.ok (value,after)) :
      Alpha (sampleToL value)
  | resumed (self after : AspisR1CanonicalReader.Reader) (value : ReaderE)
      (h : AspisR1CanonicalReader.Reader.e self=.ok (.Ok value,after)) : Alpha (readerToL value)

inductive Extra : L.K → Prop
  | semantic {H : Type} (digest : AspisR1PublicPreparation.aspis_core.Digest32 H)
      (self after : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
      (record : AspisR1PublicPreparation.r1_wire.ValidatedRecord) (value : PublicK)
      (h : AspisR1PublicPreparation.r1_wire.SemanticTranscript.semantic_validated digest self record=.ok (.Ok value,after)) :
      Extra (publicKToL value)
  | resumed (self after : AspisR1CanonicalKReader.Reader) (value : ReaderK)
      (h : AspisR1CanonicalKReader.Reader.k self=.ok (.Ok value,after)) : Extra (readerKToL value)

theorem alpha_canonical (value : L.E) (h : Alpha value) : canonicalE value := by
  cases h with
  | sampled digest self after row payload value hs =>
    have hc := CuSavingsCanonicalSampler.scalar_success digest self after row payload false value hs
    rcases hc with ⟨⟨ha,hb,hc,hd⟩,⟨he,hf,hg,hh⟩⟩
    exact ⟨⟨⟨ha,hb⟩,⟨hc,hd⟩⟩,⟨⟨he,hf⟩,⟨hg,hh⟩⟩⟩
  | resumed self after value hs => exact CuSavingsCanonicalReader.e_success self after value hs

theorem extra_canonical (value : L.K) (h : Extra value) : canonicalK value := by
  cases h with
  | semantic digest self after record value hs =>
    exact AspisR1PublicPreparation.SemanticCallSelectedCanonical.semantic_success_selected_canonical digest self after record value hs
  | resumed self after value hs =>
    obtain ⟨ha,hb,hc,hd⟩ := CuSavingsCanonicalKReader.k_success self after value hs
    exact ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩

theorem alpha_powers (value : L.E) (h : Alpha value) :
    ∃ out,CuSavingsLibraCaller.powersCaller value=.ok out ∧ ∀ i,i<4 →
      canonicalE (CuSavingsLibraSourceControl.lookup out AspisR1Libra.field.wide_exact.WideExact.ZERO i) ∧
      decodeEL (CuSavingsLibraSourceControl.lookup out AspisR1Libra.field.wide_exact.WideExact.ZERO i)=(decodeEL value)^i :=
  CuSavingsLibraCaller.powers_success value (alpha_canonical value h)

#print axioms alpha_canonical
#print axioms extra_canonical
#print axioms alpha_powers
end AspisR1.CuSavingsLibraOrigins
