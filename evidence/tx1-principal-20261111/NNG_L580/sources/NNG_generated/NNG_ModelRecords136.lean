import NNG_ModelTail136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)
theorem success_r8 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint) (vr2 : r1_wire.ValidatedRecord) (r7 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_r8 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 transcript2 val4 vr2 r7=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_r8 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT10 transcript2) (toT2 val4) (toT14 vr2) (NMP_ResultTransport.inner toT14 toT13 r7)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_r8 at returned
 obtain ⟨reply,decode,tail⟩ := bind_out _ _ _ returned
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok before=>
   cases r7 with
   | Err e=>
     change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
     cases tail
   | Ok vr3=>
     change NNG_SourceSuffixes.f_r9 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 transcript2 val4 before vr3=.ok (.Ok out) at tail
     have old := congrArg (outer (NMP_ResultTransport.inner (arr toT1) toT13)) decode
     change outer (NMP_ResultTransport.inner (arr toT1) toT13) (NNG_ModelDecode.call 29#usize vr2 0#usize)=_ at old
     rw [NNG_LegacyCalls136.decode] at old
     simp only [outer,NMP_ResultTransport.inner] at old
     unfold NNG_LegacySuffix136.f_r8
     rw [old,bind_tc_ok]
     exact success_r9 env s alpha val1 val3 state_before_z0 transcript2 val4 before vr3 out tail
#print axioms success_r8
theorem success_r7 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (transcript2 : r1_wire.SemanticTranscript H) (val4 : aspis_core.circle.SecureCirclePoint)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_r7 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 transcript2 val4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_r7 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT10 transcript2) (toT2 val4)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_r7 at returned
 obtain ⟨reply,record,tail⟩ := bind_out _ _ _ returned
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok vr2=>
   change NNG_SourceSuffixes.f_r8 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 transcript2 val4 vr2 (.Ok vr2)=.ok (.Ok out) at tail
   have old := congrArg (outer (NMP_ResultTransport.inner toT14 toT13)) record
   change outer (NMP_ResultTransport.inner toT14 toT13) (NNG_Install.validatedRecord s.prefixValue 26#u8)=_ at old
   rw [NNG_Install.record_same] at old
   simp only [outer,NMP_ResultTransport.inner] at old
   unfold NNG_LegacySuffix136.f_r7
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_r8 env s alpha val1 val3 state_before_z0 transcript2 val4 vr2 (.Ok vr2) out tail
#print axioms success_r7
theorem success_r6 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (vr1 : r1_wire.ValidatedRecord)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_r6 (NNG_ConcreteCalls136.calls env) s alpha transcript1 val1 val3 state_before_z0 vr1=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_r6 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) state_before_z0 (toT14 vr1)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_r6 at returned
 obtain ⟨pair,circle,tail⟩ := bind_out _ _ _ returned
 rcases pair with ⟨reply,t2⟩
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok z0=>
   change NNG_SourceSuffixes.f_r7 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 t2 z0=.ok (.Ok out) at tail
   have old := congrArg (outer NNG_ModelCircle.lowerReply) circle
   change outer NNG_ModelCircle.lowerReply (NNG_ModelCircle.call s.digest transcript1 vr1)=_ at old
   rw [NNG_LegacyCalls136.circle env] at old
   simp only [outer,NNG_ModelCircle.lowerReply,NMP_ResultTransport.inner] at old
   unfold NNG_LegacySuffix136.f_r6
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_r7 env s alpha val1 val3 state_before_z0 t2 z0 out tail
#print axioms success_r6
theorem success_state_before_z0 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_state_before_z0 (NNG_ConcreteCalls136.calls env) s alpha transcript1 val1 val3 r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_state_before_z0 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_state_before_z0 at returned
 obtain ⟨state,native,tail⟩ := bind_out _ _ _ returned
 cases r4 with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok vr1=>
   change NNG_SourceSuffixes.f_r6 (NNG_ConcreteCalls136.calls env) s alpha transcript1 val1 val3 state vr1=.ok (.Ok out) at tail
   have old := native
   change AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state (NNG_Install.digest s.digest) (toT10 transcript1)=.ok state at old
   unfold NNG_LegacySuffix136.f_state_before_z0
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_r6 env s alpha transcript1 val1 val3 state vr1 out tail
#print axioms success_state_before_z0
theorem success_mark4 {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_mark4 (NNG_ConcreteCalls136.calls env) s alpha transcript1 val1 val3 r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_mark4 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 change NNG_SourceSuffixes.f_state_before_z0 (NNG_ConcreteCalls136.calls env) s alpha transcript1 val1 val3 r4=.ok (.Ok out) at returned
 unfold NNG_LegacySuffix136.f_mark4
 dsimp only [NNG_LegacyConfig136.parent]
 rw [LIB_Mark.result,bind_tc_ok]
 exact success_state_before_z0 env s alpha transcript1 val1 val3 r4 out returned
#print axioms success_mark4
theorem success_terminalGuard {H W : Type} (env : RSL.Env) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (b : Bool) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_terminalGuard (NNG_ConcreteCalls136.calls env) s alpha transcript1 val1 val3 b r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_terminalGuard (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) b (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 cases b with
 | false=>exact success_mark4 env s alpha transcript1 val1 val3 r4 out returned
 | true=>cases returned
#print axioms success_terminalGuard
theorem success_b {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (masked_terminal : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_b (NNG_ConcreteCalls136.calls env) s running masked_terminal alpha transcript1 val1 val3 r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_b (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 masked_terminal) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 simp only [NNG_SourceSuffixes.f_b,NNG_ConcreteCalls136.calls,NNG_Equality136.terminal_guard,bind_tc_ok] at returned
 unfold NNG_LegacySuffix136.f_b
 dsimp only [NNG_LegacyConfig136.parent]
 rw [NNG_LegacyEquality136.ne,bind_tc_ok]
 exact success_terminalGuard env s alpha transcript1 val1 val3 (decide (running≠masked_terminal)) r4 out returned
#print axioms success_b
end AspisR1.NNG_ModelSuccess136
