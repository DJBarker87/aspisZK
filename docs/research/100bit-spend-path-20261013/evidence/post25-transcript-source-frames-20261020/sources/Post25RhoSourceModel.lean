import Post25TranscriptSuccess
import ExtractedSourceSemanticSampler
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Post25Transcript.RhoSourceModel
abbrev PrepQM := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev QM := aspis_core.field.QM31
abbrev E := aspis_core.field.WideExact
abbrev Bytes32 := Array U8 32#usize

def fromPrep (q : PrepQM) : QM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toPrep (q : QM) : PrepQM := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem toPrep_fromPrep (q : PrepQM) : toPrep (fromPrep q) = q := by
  cases q with | mk a b => cases a; cases b; rfl

def decode (q : QM) : AspisV8R15.ExactTowerBase.QM31Exact :=
  AspisR1.ExtractedCurrentQM31Exact.decode
    (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
      (AspisR1PublicPreparation.SamplerTransport.toOld (toPrep q)))

def operations (gamma ordinary : Bytes32 → Result E) (embed : QM → Result E) : SamplerOps where
  gamma := gamma
  ordinary := ordinary
  qm31 := fun block => do
    let q ← AspisR1PublicPreparation.sampler.qm31_sample block
    .ok (fromPrep q)
  embed := embed

theorem scalar_k_model_success {H : Type} (D : aspis_core.Digest32 H)
    (gamma ordinary : Bytes32 → Result E) (embed : QM → Result E)
    (self after : transcript.Transcript H) (payload : Slice U8) (out : QM)
    (h : transcript.Transcript.scalar_k (operations gamma ordinary embed) D self 32#u8 payload =
      .ok (out,after)) :
    ∃ block absorbed state,
      D.digest self.hash (TranscriptSuccess.absorbParts self.state 192#u8 payload) = .ok absorbed ∧
      D.digest self.hash (TranscriptSuccess.readParts absorbed 1#u8) = .ok block ∧
      D.digest self.hash (TranscriptSuccess.readParts absorbed 2#u8) = .ok state ∧
      after = {self with state := state} ∧
      decode out = R0P.SemSource.qm31Sample
        (AspisV8R19.SqueezeOracleBridge.decodeState block) := by
  obtain ⟨block,embedded,hblock,hsample,hembed⟩ :=
    TranscriptSuccess.scalar_k_success (operations gamma ordinary embed) D self after 32#u8 payload out h
  obtain ⟨absorbed,state,habs,hread,hstate,hafter⟩ :=
    TranscriptSuccess.block_success D self after 32#u8 192#u8 payload block rfl hblock
  obtain ⟨q,hq,hcanonical,hcoordinates⟩ :=
    AspisR1PublicPreparation.SamplerTransport.sample_total block
  change (do let q ← AspisR1PublicPreparation.sampler.qm31_sample block
             .ok (fromPrep q)) = .ok out at hsample
  rw [hq] at hsample
  have heq : fromPrep q = out := Result.ok.inj hsample
  subst out
  refine ⟨block,absorbed,state,habs,hread,hstate,hafter,?_⟩
  unfold decode
  rw [toPrep_fromPrep]
  exact AspisR1PublicPreparation.SourceSemanticSampler.sample_qm31 block q hq
#print axioms toPrep_fromPrep
#print axioms scalar_k_model_success
end AspisR1Post25Transcript.RhoSourceModel
