from pathlib import Path
import runpy
E=Path(__file__).resolve().parent
G=runpy.run_path(str(E/'NNG_model_success136.py'));theorem=G['theorem']
s='''import NNG_ModelTail136
import NNG_LegacyNe136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)
'''
s+=theorem('r8')+''' unfold NNG_SourceSuffixes.f_r8 at returned
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
'''
s+=theorem('r7')+''' unfold NNG_SourceSuffixes.f_r7 at returned
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
'''
s+=theorem('r6')+''' unfold NNG_SourceSuffixes.f_r6 at returned
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
'''
s+=theorem('state_before_z0')+''' unfold NNG_SourceSuffixes.f_state_before_z0 at returned
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
'''
s+=theorem('mark4')+''' change NNG_SourceSuffixes.f_state_before_z0 (NNG_ConcreteCalls136.calls env) s alpha transcript1 val1 val3 r4=.ok (.Ok out) at returned
 unfold NNG_LegacySuffix136.f_mark4
 dsimp only [NNG_LegacyConfig136.parent]
 rw [LIB_Mark.result,bind_tc_ok]
 exact success_state_before_z0 env s alpha transcript1 val1 val3 r4 out returned
#print axioms success_mark4
'''
s+=theorem('terminalGuard')+''' cases b with
 | false=>exact success_mark4 env s alpha transcript1 val1 val3 r4 out returned
 | true=>cases returned
#print axioms success_terminalGuard
'''
s+=theorem('b')+''' simp only [NNG_SourceSuffixes.f_b,NNG_ConcreteCalls136.calls,NNG_Equality136.terminal_guard,bind_tc_ok] at returned
 unfold NNG_LegacySuffix136.f_b
 dsimp only [NNG_LegacyConfig136.parent]
 rw [NNG_LegacyNe136.ne,bind_tc_ok]
 exact success_terminalGuard env s alpha transcript1 val1 val3 (decide (running≠masked_terminal)) r4 out returned
#print axioms success_b
end AspisR1.NNG_ModelSuccess136
'''
(E/'NNG_ModelRecords136.lean').write_text(s)
