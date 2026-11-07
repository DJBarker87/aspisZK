import NNG_ModelRoot136
import NNG_LegacyEquality136
import LIB_Mark
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)
theorem success_circleGuard {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) (b1 : Bool)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_circleGuard (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 b1=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_circleGuard (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT2 val4) (arr toT1 val5) (toT10 transcript3) (toT2 val6) b1=.ok (.Ok (toT11 out)) := by
 cases b1 with
 | false=>exact success_r10 env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 out returned
 | true=>cases returned
#print axioms success_circleGuard
theorem success_b1 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_b1 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_b1 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT2 val4) (arr toT1 val5) (toT10 transcript3) (toT2 val6)=.ok (.Ok (toT11 out)) := by
 change NNG_SourceSuffixes.f_circleGuard (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 (decide (val4=val6))=.ok (.Ok out) at returned
 unfold NNG_LegacySuffix136.f_b1
 dsimp only [NNG_LegacyConfig136.parent]
 rw [NNG_LegacyEquality136.point,bind_tc_ok]
 exact success_circleGuard env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 (decide (val4=val6)) out returned
#print axioms success_b1
theorem success_mark5 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_mark5 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_mark5 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT2 val4) (arr toT1 val5) (toT10 transcript3) (toT2 val6)=.ok (.Ok (toT11 out)) := by
 change NNG_SourceSuffixes.f_b1 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6=.ok (.Ok out) at returned
 unfold NNG_LegacySuffix136.f_mark5
 dsimp only [NNG_LegacyConfig136.parent]
 rw [LIB_Mark.result,bind_tc_ok]
 exact success_b1 env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 out returned
#print axioms success_mark5
theorem success_r9 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (vr3 : r1_wire.ValidatedRecord)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_r9 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 transcript2 val4 val5 vr3=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_r9 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT10 transcript2) (toT2 val4) (arr toT1 val5) (toT14 vr3)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_r9 at returned
 obtain ⟨pair,circle,tail⟩ := bind_out _ _ _ returned
 rcases pair with ⟨reply,t3⟩
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok z1=>
   change NNG_SourceSuffixes.f_mark5 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 t3 z1=.ok (.Ok out) at tail
   have old := congrArg (outer NNG_ModelCircle.lowerReply) circle
   change outer NNG_ModelCircle.lowerReply (NNG_ModelCircle.call s.digest transcript2 vr3)=_ at old
   rw [NNG_LegacyCalls136.circle env] at old
   simp only [outer,NNG_ModelCircle.lowerReply,NMP_ResultTransport.inner] at old
   unfold NNG_LegacySuffix136.f_r9
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_mark5 env s alpha val1 val3 state_before_z0 val4 val5 t3 z1 out tail
#print axioms success_r9
end AspisR1.NNG_ModelSuccess136
