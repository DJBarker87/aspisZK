import Post25TranscriptSuccess
import IndexedOrdinaryCandidateDensity
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Post25Transcript.OrdinaryCandidateSourceModel
abbrev CandidateQM := AspisR1Post25Sampler.field.QM31
abbrev CandidateWide := AspisR1Post25Sampler.field.WideExact
abbrev QM := aspis_core.field.QM31
abbrev E := aspis_core.field.WideExact
abbrev Bytes32 := Array U8 32#usize

def fromQM (q : CandidateQM) : QM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toQM (q : QM) : CandidateQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromWide (v : CandidateWide) : E := ⟨fromQM v.c0,fromQM v.c1⟩
def toWide (v : E) : CandidateWide := ⟨toQM v.c0,toQM v.c1⟩
theorem toWide_fromWide (v : CandidateWide) : toWide (fromWide v) = v := by
  cases v with | mk a b => cases a with | mk a0 a1 => cases b with | mk b0 b1 =>
    cases a0; cases a1; cases b0; cases b1; rfl

def decode (v : E) : AspisWideTower.WideExact :=
  AspisR1.ExtractedQM31SamplerIndexedDecode8RetainedBridgeV3.candidateWideToExact (toWide v)

def operations (gamma : Bytes32 → Result E) (qm31 : Bytes32 → Result QM)
    (embed : QM → Result E) : SamplerOps where
  gamma := gamma
  ordinary := fun block => do
    let value ← AspisR1Post25Sampler.sampler.ordinary_sample block
    .ok (fromWide value)
  qm31 := qm31
  embed := embed

theorem ordinary_model_total (block : Bytes32) :
    ∃ value : E,
      (operations (fun _ => .div) (fun _ => .div) (fun _ => .div)).ordinary block = .ok value ∧
      decode value = R0C.ModuloField.ordinary
        (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  have hround := AspisV8R19.SqueezeOracleBridge.array_roundtrip block
  obtain ⟨value,hvalue,hmodel⟩ :=
    AspisR1.IndexedOrdinaryCandidateDensity.encoded_output
      (AspisV8R19.SqueezeOracleBridge.decodeState block)
  rw [hround] at hvalue
  refine ⟨fromWide value,?_,?_⟩
  · change (do let v ← AspisR1Post25Sampler.sampler.ordinary_sample block; .ok (fromWide v)) = .ok (fromWide value)
    rw [hvalue]
    rfl
  · unfold decode
    rw [toWide_fromWide]
    exact hmodel

theorem scalar_model_success {H : Type} (D : aspis_core.Digest32 H)
    (gamma : Bytes32 → Result E) (qm31 : Bytes32 → Result QM) (embed : QM → Result E)
    (self after : transcript.Transcript H) (row tag : U8) (payload : Slice U8) (out : E)
    (htag : (160#u8 + row : Result U8) = .ok tag)
    (h : transcript.Transcript.scalar (operations gamma qm31 embed) D self row payload false =
      .ok (out,after)) :
    ∃ block absorbed state,
      D.digest self.hash (TranscriptSuccess.absorbParts self.state tag payload) = .ok absorbed ∧
      D.digest self.hash (TranscriptSuccess.readParts absorbed 1#u8) = .ok block ∧
      D.digest self.hash (TranscriptSuccess.readParts absorbed 2#u8) = .ok state ∧
      after = {self with state := state} ∧
      decode out = R0C.ModuloField.ordinary
        (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  obtain ⟨block,hblock,hsample⟩ :=
    TranscriptSuccess.scalar_success (operations gamma qm31 embed) D self after row payload false out h
  obtain ⟨absorbed,state,habs,hread,hstate,hafter⟩ :=
    TranscriptSuccess.block_success D self after row tag payload block htag hblock
  obtain ⟨value,hvalue,hmodel⟩ := ordinary_model_total block
  change (operations gamma qm31 embed).ordinary block = .ok out at hsample
  have heq : value = out := Result.ok.inj (hvalue.symm.trans hsample)
  subst out
  exact ⟨block,absorbed,state,habs,hread,hstate,hafter,hmodel⟩
#print axioms toWide_fromWide
#print axioms ordinary_model_total
#print axioms scalar_model_success
end AspisR1Post25Transcript.OrdinaryCandidateSourceModel
