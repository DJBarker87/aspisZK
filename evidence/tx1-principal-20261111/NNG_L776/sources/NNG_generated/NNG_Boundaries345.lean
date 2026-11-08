import NNG_Calls345
import NNG_DecoderGraph345
import NMT_345MapEncoder
import NMT_R2_ValidatorTotal
import NMT_R2_EncoderTotal
import NMT_345BoundaryDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Boundaries345
open Aeneas Aeneas.Std NMT_345

theorem validator {W : Type} (s : Decoded W) (env : RSL.Env) :
 raw07 (NNG_Calls345.calls env) s=
 match NMT_R2_ValidatorTotal.fresh s.statement with
 | .Ok _=>raw08 (NNG_Calls345.calls env) s
 | .Err _=>.ok (.Err .InvalidAccountData) := by
 rw [validator_call]
 change (do let r ← validateCall s.statement;mapValidator (NNG_Calls345.calls env) ⟨s,r⟩)=_
 rw [NMT_R2_ValidatorTotal.emitted]
 simp only [bind_tc_ok]
 exact validator_map_std (NNG_Calls345.calls env) ⟨s,NMT_R2_ValidatorTotal.fresh s.statement⟩
#print axioms validator

theorem encoder {W : Type} (s : Decoded W) (env : RSL.Env) :
 raw08 (NNG_Calls345.calls env) s=
 match NMT_R2_EncoderTotal.value (commonValue s.statement).lane_transition.candidate_afterstate with
 | .Ok candidate=>raw09 (NNG_Calls345.calls env) ⟨s,candidate⟩
 | .Err _=>.ok (.Err .InvalidAccountData) := by
 rw [common_encoder_calls]
 change (do let common ← commonCall s.statement
            let r ← encodeCall common.lane_transition.candidate_afterstate
            mapEncoder (NNG_Calls345.calls env) ⟨s,common,r⟩)=_
 unfold commonCall
 simp only [bind_tc_ok]
 rw [NMT_R2_EncoderTotal.source]
 simp only [bind_tc_ok]
 exact encoder_map_std (NNG_Calls345.calls env)
  ⟨s,commonValue s.statement,NMT_R2_EncoderTotal.value (commonValue s.statement).lane_transition.candidate_afterstate⟩
#print axioms encoder

theorem decoder {W : Type} (s : PublicData W) (env : RSL.Env) :
 raw06 (NNG_Calls345.calls env) s=
 tryStep (.ok (NNG_DecoderGraph345.reply (LIBC_S1.decode (LIB_Carriers.bytes s.publicData))))
 (fun st=>raw07 (NNG_Calls345.calls env) ⟨s,st⟩) := by
 rw [boundaryDecode]
 change tryStep (decodeCall s.publicData) _=_
 rw [NNG_DecoderGraph345.source]
#print axioms decoder
end AspisR1.NNG_Boundaries345
