import NNG_ModelRecords136
import NNG_LegacyArrays136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)
theorem success_masked_terminal {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (q2 : Q) (q3 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_masked_terminal (NNG_ConcreteCalls136.calls env) s running q2 q3 alpha transcript1 val1 val3 r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_masked_terminal (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 q2) (toT1 q3) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_masked_terminal at returned
 obtain ⟨masked,native,tail⟩ := bind_out _ _ _ returned
 change NNG_InstallArithmetic.add q2 q3=.ok masked at native
 have old := congrArg (outer toT1) native
 rw [NNG_InstallArithmetic.add_same] at old
 simp only [outer] at old
 unfold NNG_LegacySuffix136.f_masked_terminal
 dsimp only [NNG_LegacyConfig136.boundaries,NNG_LegacyConfig136.parent,NNG_Transport.toT3]
 rw [old,bind_tc_ok]
 exact success_b env s running masked alpha transcript1 val1 val3 r4 out tail
#print axioms success_masked_terminal
theorem success_q3 {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (q2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_q3 (NNG_ConcreteCalls136.calls env) s running q2 alpha transcript1 val1 val3 r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_q3 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 q2) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_q3 at returned
 obtain ⟨q3,native,tail⟩ := bind_out _ _ _ returned
 have old := NNG_LegacyArrays136.returned toT1 val3 28#usize (by decide) q3 native
 unfold NNG_LegacySuffix136.f_q3
 rw [old,bind_tc_ok]
 exact success_masked_terminal env s running q2 q3 alpha transcript1 val1 val3 r4 out tail
#print axioms success_q3
theorem success_q2 {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (mask : Q) (q1 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_q2 (NNG_ConcreteCalls136.calls env) s running mask q1 alpha transcript1 val1 val3 r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_q2 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 mask) (toT1 q1) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_q2 at returned
 obtain ⟨q2,native,tail⟩ := bind_out _ _ _ returned
 change NNG_InstallArithmetic.add mask q1=.ok q2 at native
 have old := congrArg (outer toT1) native
 rw [NNG_InstallArithmetic.add_same] at old
 simp only [outer] at old
 unfold NNG_LegacySuffix136.f_q2
 dsimp only [NNG_LegacyConfig136.boundaries,NNG_LegacyConfig136.parent,NNG_Transport.toT3]
 rw [old,bind_tc_ok]
 exact success_q3 env s running q2 alpha transcript1 val1 val3 r4 out tail
#print axioms success_q2
theorem success_q1 {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_q1 (NNG_ConcreteCalls136.calls env) s running val2 mask alpha transcript1 val1 val3 r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_q1 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 val2) (toT1 mask) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 val3) (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_q1 at returned
 obtain ⟨q1,native,tail⟩ := bind_out _ _ _ returned
 change NNG_InstallArithmetic.mul s.challenges.eta val2=.ok q1 at native
 have old := congrArg (outer toT1) native
 rw [NNG_InstallArithmetic.mul_same] at old
 simp only [outer] at old
 unfold NNG_LegacySuffix136.f_q1
 dsimp only [NNG_LegacyConfig136.boundaries,NNG_LegacyConfig136.parent,NNG_Transport.toT3]
 rw [old,bind_tc_ok]
 exact success_q2 env s running mask q1 alpha transcript1 val1 val3 r4 out tail
#print axioms success_q1
theorem success_r5 {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (vr : r1_wire.ValidatedRecord) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_r5 (NNG_ConcreteCalls136.calls env) s running val2 mask alpha transcript1 val1 vr r4=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_r5 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 val2) (toT1 mask) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (toT14 vr) (NMP_ResultTransport.inner toT14 toT13 r4)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_r5 at returned
 obtain ⟨reply,decode,tail⟩ := bind_out _ _ _ returned
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok extra=>
   change NNG_SourceSuffixes.f_q1 (NNG_ConcreteCalls136.calls env) s running val2 mask alpha transcript1 val1 extra r4=.ok (.Ok out) at tail
   have old := congrArg (outer (NMP_ResultTransport.inner (arr toT1) toT13)) decode
   change outer (NMP_ResultTransport.inner (arr toT1) toT13) (NNG_ModelDecode.call 29#usize vr 87#usize)=_ at old
   rw [NNG_LegacyCalls136.decode] at old
   simp only [outer,NMP_ResultTransport.inner] at old
   unfold NNG_LegacySuffix136.f_r5
   rw [old,bind_tc_ok]
   exact success_q1 env s running val2 mask alpha transcript1 val1 extra r4 out tail
#print axioms success_r5
theorem success_r4 {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (val2 : Q) (mask : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_r4 (NNG_ConcreteCalls136.calls env) s running val2 mask alpha transcript1 val1=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_r4 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 val2) (toT1 mask) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_r4 at returned
 obtain ⟨reply,record,tail⟩ := bind_out _ _ _ returned
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok vr=>
   change NNG_SourceSuffixes.f_r5 (NNG_ConcreteCalls136.calls env) s running val2 mask alpha transcript1 val1 vr (.Ok vr)=.ok (.Ok out) at tail
   have old := congrArg (outer (NMP_ResultTransport.inner toT14 toT13)) record
   change outer (NMP_ResultTransport.inner toT14 toT13) (NNG_Install.validatedRecord s.prefixValue 25#u8)=_ at old
   rw [NNG_Install.record_same] at old
   simp only [outer,NMP_ResultTransport.inner] at old
   unfold NNG_LegacySuffix136.f_r4
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_r5 env s running val2 mask alpha transcript1 val1 vr (.Ok vr) out tail
#print axioms success_r4
theorem success_mask {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (val2 : Q) (q : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_mask (NNG_ConcreteCalls136.calls env) s running val2 q alpha transcript1 val1 a a1=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_mask (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 val2) (toT1 q) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 a) (arr toT1 a1)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_mask at returned
 obtain ⟨mask,native,tail⟩ := bind_out _ _ _ returned
 change NNG_ModelMask.call a a1 q alpha=.ok mask at native
 have old := congrArg (outer toT1) native
 rw [NNG_ModelMask.call_model] at old
 simp only [outer] at old
 unfold NNG_LegacySuffix136.f_mask
 dsimp only [NNG_LegacyConfig136.boundaries,NNG_LegacyConfig136.parent,NNG_Transport.toT3]
 rw [old,bind_tc_ok]
 exact success_r4 env s running val2 mask alpha transcript1 val1 out tail
#print axioms success_mask
theorem success_q {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha) (a2 : K29)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_q (NNG_ConcreteCalls136.calls env) s running val2 alpha transcript1 val1 a a1 a2=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_q (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 val2) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 a) (arr toT1 a1) (arr toT1 a2)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_q at returned
 obtain ⟨q,native,tail⟩ := bind_out _ _ _ returned
 have old := NNG_LegacyArrays136.returned toT1 a2 27#usize (by decide) q native
 unfold NNG_LegacySuffix136.f_q
 rw [old,bind_tc_ok]
 exact success_mask env s running val2 q alpha transcript1 val1 a a1 out tail
#print axioms success_q
theorem success_a2 {H W : Type} (env : RSL.Env) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) (a1 : Alpha)
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_a2 (NNG_ConcreteCalls136.calls env) s running val2 alpha transcript1 val1 a a1=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_a2 (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  (toT1 running) (toT1 val2) (arr toT1 alpha) (toT10 transcript1) (NNG_InstallClaims.lowerClaims val1) (arr toT1 a) (arr toT1 a1)=.ok (.Ok (toT11 out)) := by
 unfold NNG_SourceSuffixes.f_a2 at returned
 obtain ⟨a2,native,tail⟩ := bind_out _ _ _ returned
 have old := NNG_LegacyArrays136.returned (arr toT1) val1 0#usize (by decide) a2 native
 unfold NNG_LegacySuffix136.f_a2
 change (do let a2 ← Array.index_usize (arr (arr toT1) val1) 0#usize; _)=_
 rw [old,bind_tc_ok]
 exact success_q env s running val2 alpha transcript1 val1 a a1 a2 out tail
#print axioms success_a2
end AspisR1.NNG_ModelSuccess136
