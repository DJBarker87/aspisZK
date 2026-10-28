import NDO_JFp_FinalAudit
set_option autoImplicit false
namespace AspisR1.JFm_Query00Semantic
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge

def record : r1_wire.ValidatedRecord := ⟨0#u8,JFw_NativeRow00.record⟩

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q : AspisR1PublicPreparation.aspis_core.field.QM31,
    r1_wire.SemanticTranscript.semantic_validated D0
      (⟨encodeState JFr_SeedBoundary.numeric,hash,0#u8⟩ : r1_wire.SemanticTranscript Hash)
      record=ok (.Ok q,
        (⟨encodeState JFp_Query00Source.ratchet,hash,1#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    ExtractedQM31SamplerCorrect.coordinates (AspisR1PublicPreparation.SamplerTransport.toOld q)=
        [399501241,284689285,1852519329,449773828] := by
  obtain ⟨q,call,coords⟩ := JFp_Query00Rank.sampled
  refine ⟨q,?_,coords⟩
  simp only [r1_wire.SemanticTranscript.semantic_validated,record,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
  rw [if_neg (by change ¬(0:Nat)>24;omega)]
  rw [JFp_Query00Source.source,bind_tc_ok]
  change (do let v ← AspisR1PublicPreparation.sampler.qm31_sample (encodeState JFp_Query00Source.block)
             ok ((core.result.Result.Ok v : core.result.Result aspis_core.field.QM31 r1_wire.Error),
               (⟨encodeState JFp_Query00Source.ratchet,hash,1#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]

#print axioms source
end AspisR1.JFm_Query00Semantic
