import NNG_StageValues137
import NNG_Caller136From137
import NNG_Parse137
import LIB_VDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Reached137
open Aeneas Aeneas.Std Result NMP_prepare NMP_Transport

theorem parse_eval (a : NNG_Data137.Args) (domain : RSL.TX1_137.Domain NNG_Data137.VL a)
    (raw : r1_wire.Prefix) (returned : NMP_Install138.parse (NNG_Data137.bytes a.bytes)=.ok (.Ok raw)) :
    ∃ p : LIB_VCarriers.Prefix, LIB_VParsePrefix.eval a.bytes=.ok p ∧
      raw=fromT13 (LIB_VCarriers.prefixRaw p) := by
  obtain ⟨p,model,same⟩ := NNG_Parse137.succeeded _ raw returned
  rw [NNG_Data137.bytes_exact a domain] at model
  exact ⟨p,by simp only [LIB_VParsePrefix.eval,model,LIB_VResult.value,id_eq],same⟩
#print axioms parse_eval

theorem begin_raw (fallback : LIB_VCarriers.QM31) (env : RSL.Env) (p : LIB_VCarriers.Prefix)
    (t : r1_wire.SemanticTranscript Unit) (c : aspis_core.state_only_prefix.r0.Challenges)
    (after : r1_wire.SemanticTranscript Unit)
    (returned : NMP_Install150.begin_ (NNG_PublicSource137.digest env) (fromT13 (LIB_VCarriers.prefixRaw p)) t = .ok (.Ok c,after)) :
    LIB_VCarriers.challengesRaw (NNG_ChallengeProjection137.project fallback (toT3 c))=toT3 c := by
  have value := NNG_BeginSource137.value env (fromT13 (LIB_VCarriers.prefixRaw p)) t
  rw [returned,fromT13_inverse] at value
  have native : AspisR1PublicPreparation.r1_wire.begin (LIB_VCode.digest env) (LIB_VCarriers.prefixRaw p) (toT10 t)=
      .ok (.Ok (toT3 c),toT10 after) := value.symm
  have canonical := LIB_VChallenges.begin_canonical (LIB_VCode.digest env) p (toT10 t) (toT10 after) (toT3 c) native
  rw [NNG_ChallengeProjection137.lifted fallback _ canonical]
  exact LIB_VChallenges.raw_lift _ canonical
#print axioms begin_raw
end AspisR1.NNG_Reached137
