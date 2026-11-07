from pathlib import Path
import runpy
E=Path(__file__).resolve().parent
G=runpy.run_path(str(E/'NNG_model_success136.py'))
theorem=G['theorem']
s='''import NNG_ModelRoot136
import NNG_LegacyEquality136
import LIB_Mark
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)
'''
s+=theorem('circleGuard')+''' cases b1 with
 | false=>exact success_r10 env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 out returned
 | true=>cases returned
#print axioms success_circleGuard
'''
s+=theorem('b1')+''' change NNG_SourceSuffixes.f_circleGuard (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 (decide (val4=val6))=.ok (.Ok out) at returned
 unfold NNG_LegacySuffix136.f_b1
 dsimp only [NNG_LegacyConfig136.parent]
 rw [NNG_LegacyEquality136.point,bind_tc_ok]
 exact success_circleGuard env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 (decide (val4=val6)) out returned
#print axioms success_b1
'''
s+=theorem('mark5')+''' change NNG_SourceSuffixes.f_b1 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6=.ok (.Ok out) at returned
 unfold NNG_LegacySuffix136.f_mark5
 dsimp only [NNG_LegacyConfig136.parent]
 rw [LIB_Mark.result,bind_tc_ok]
 exact success_b1 env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 out returned
#print axioms success_mark5
'''
s+=theorem('r9')+''' unfold NNG_SourceSuffixes.f_r9 at returned
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
'''
(E/'NNG_ModelTail136.lean').write_text(s)
