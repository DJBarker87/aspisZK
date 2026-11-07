from pathlib import Path
import runpy
E=Path(__file__).resolve().parent
G=runpy.run_path(str(E/'NNG_model_success136.py'));theorem=G['theorem']
s='''import NNG_ModelRecords136
import NNG_LegacyArrays136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)
'''
def arithmetic(name,value,call,lemma,next_,args):
 return theorem(name)+f''' unfold NNG_SourceSuffixes.f_{name} at returned
 obtain ⟨{value},native,tail⟩ := bind_out _ _ _ returned
 change {call}=.ok {value} at native
 have old := congrArg (outer toT1) native
 rw [{lemma}] at old
 simp only [outer] at old
 unfold NNG_LegacySuffix136.f_{name}
 dsimp only [NNG_LegacyConfig136.boundaries,NNG_LegacyConfig136.parent,NNG_Transport.toT3]
 rw [old,bind_tc_ok]
 exact success_{next_} env s {args} out tail
#print axioms success_{name}
'''
s+=arithmetic('masked_terminal','masked','NNG_InstallArithmetic.add q2 q3','NNG_InstallArithmetic.add_same','b','running masked alpha transcript1 val1 val3 r4')
s+=theorem('q3')+''' unfold NNG_SourceSuffixes.f_q3 at returned
 obtain ⟨q3,native,tail⟩ := bind_out _ _ _ returned
 have old := NNG_LegacyArrays136.returned toT1 val3 28#usize (by decide) q3 native
 unfold NNG_LegacySuffix136.f_q3
 rw [old,bind_tc_ok]
 exact success_masked_terminal env s running q2 q3 alpha transcript1 val1 val3 r4 out tail
#print axioms success_q3
'''
s+=arithmetic('q2','q2','NNG_InstallArithmetic.add mask q1','NNG_InstallArithmetic.add_same','q3','running q2 alpha transcript1 val1 val3 r4')
s+=arithmetic('q1','q1','NNG_InstallArithmetic.mul s.challenges.eta val2','NNG_InstallArithmetic.mul_same','q2','running mask q1 alpha transcript1 val1 val3 r4')
s+=theorem('r5')+''' unfold NNG_SourceSuffixes.f_r5 at returned
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
'''
s+=theorem('r4')+''' unfold NNG_SourceSuffixes.f_r4 at returned
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
'''
s+=arithmetic('mask','mask','NNG_ModelMask.call a a1 q alpha','NNG_ModelMask.call_model','r4','running val2 mask alpha transcript1 val1')
s+=theorem('q')+''' unfold NNG_SourceSuffixes.f_q at returned
 obtain ⟨q,native,tail⟩ := bind_out _ _ _ returned
 have old := NNG_LegacyArrays136.returned toT1 a2 27#usize (by decide) q native
 unfold NNG_LegacySuffix136.f_q
 rw [old,bind_tc_ok]
 exact success_mask env s running val2 q alpha transcript1 val1 a a1 out tail
#print axioms success_q
'''
s+=theorem('a2')+''' unfold NNG_SourceSuffixes.f_a2 at returned
 obtain ⟨a2,native,tail⟩ := bind_out _ _ _ returned
 have old := NNG_LegacyArrays136.returned (arr toT1) val1 0#usize (by decide) a2 native
 unfold NNG_LegacySuffix136.f_a2
 change (do let a2 ← Array.index_usize (arr (arr toT1) val1) 0#usize; _)=_
 rw [old,bind_tc_ok]
 exact success_q env s running val2 alpha transcript1 val1 a a1 a2 out tail
#print axioms success_a2
end AspisR1.NNG_ModelSuccess136
'''
(E/'NNG_ModelArithmetic136.lean').write_text(s)
