import NMT_345MapEncoder
import NMT_R2_EncoderObservation
set_option autoImplicit false
noncomputable section
namespace NMT_R2_345AtEncoder
open Aeneas Aeneas.Std NMT_345 RSL

def install (c : Calls) : Calls := installMapErr {c with c6 := commonCall,c9 := encodeCall}

theorem boundary {W : Type} (c : Calls) (s : Decoded W) :
 raw08 (install c) s =
 match NMT_R2_EncoderTotal.value (commonValue s.statement).lane_transition.candidate_afterstate with
 | .Ok candidate => raw09 (install c) ⟨s,candidate⟩
 | .Err _ => .ok (.Err .InvalidAccountData) := by
 rw [common_encoder_calls]
 change (do
  let common ← commonCall s.statement
  let reply ← encodeCall common.lane_transition.candidate_afterstate
  mapEncoder (install c) ⟨s,common,reply⟩) = _
 unfold commonCall
 simp only [bind_tc_ok]
 rw [NMT_R2_EncoderTotal.source]
 simp only [bind_tc_ok]
 exact encoder_map_std {c with c6 := commonCall,c9 := encodeCall}
  ⟨s,commonValue s.statement,NMT_R2_EncoderTotal.value (commonValue s.statement).lane_transition.candidate_afterstate⟩

theorem observation {W : Type} (s : Decoded W) (env : Env) :
 RS.ofOption (NMT_R2_ConcreteS1.encode s.statement) .invalidAccountData env
  (NMT_R2_EncoderObservation.run s.statement) := NMT_R2_EncoderObservation.law s.statement env
#print axioms boundary
#print axioms observation
end NMT_R2_345AtEncoder
end
