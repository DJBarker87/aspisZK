from pathlib import Path
import runpy
E=Path(__file__).resolve().parent
G=runpy.run_path(str(E/'NNG_model_success136.py'));theorem=G['theorem']
s='''import NNG_ModelArithmetic136
import NNG_LegacyHigh136
import NNG_LegacyTerminal136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)
'''
s+=theorem('a1')+''' change (do
   let high←NNG_StdArray.implementation 10#usize
       (r1_semantic.verify_finish.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 s.digest) val1
   NNG_SourceSuffixes.f_a2 (NNG_ConcreteCalls136.calls env) s running val2 alpha transcript1 val1 a high)=.ok (.Ok out) at returned
 rw [NNG_FromFnValues136.second,bind_tc_ok] at returned
 unfold NNG_LegacySuffix136.f_a1
 dsimp only [NNG_LegacyConfig136.boundaries,NNG_LegacyConfig136.parent]
 rw [NNG_LegacyHigh136.array,bind_tc_ok]
 exact success_a2 env s running val2 alpha transcript1 val1 a (NNG_FromFnValues136.high val1) out returned
#print axioms success_a1
'''
s+=theorem('a')+''' change (do
   let low←NNG_StdArray.implementation 16#usize
       (r1_semantic.verify_finish.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 s.digest) val1
   NNG_SourceSuffixes.f_a1 (NNG_ConcreteCalls136.calls env) s running val2 alpha transcript1 val1 low)=.ok (.Ok out) at returned
 rw [NNG_FromFnValues136.first,bind_tc_ok] at returned
 unfold NNG_LegacySuffix136.f_a
 dsimp only [NNG_LegacyConfig136.boundaries,NNG_LegacyConfig136.parent]
 rw [NNG_LegacyLow136.array,bind_tc_ok]
 exact success_a1 env s running val2 alpha transcript1 val1 (NNG_FromFnValues136.low val1) out returned
#print axioms success_a
'''
s+=theorem('mark3')+''' change NNG_SourceSuffixes.f_a (NNG_ConcreteCalls136.calls env) s running val2 alpha transcript1 val1=.ok (.Ok out) at returned
 unfold NNG_LegacySuffix136.f_mark3
 dsimp only [NNG_LegacyConfig136.parent]
 rw [LIB_Mark.result,bind_tc_ok]
 exact success_a env s running val2 alpha transcript1 val1 out returned
#print axioms success_mark3
'''
s+=theorem('r3')+''' cases r2 with
 | Err e=>
   change (.ok (.Err .Public) : Result (Output H))=.ok (.Ok out) at returned
   cases returned
 | Ok q=>
   change NNG_SourceSuffixes.f_mark3 (NNG_ConcreteCalls136.calls env) s running q alpha transcript1 val1=.ok (.Ok out) at returned
   exact success_mark3 env s running q alpha transcript1 val1 out returned
#print axioms success_r3
'''
s+=theorem('r2')+''' unfold NNG_SourceSuffixes.f_r2 at returned
 obtain ⟨reply,native,tail⟩ := bind_out _ _ _ returned
 change NNG_ModelTerminal.call s.publicValue val1 alpha s.challenges=.ok reply at native
 have old := congrArg (outer (NMP_ResultTransport.inner toT1 NNG_LegacyTerminal136.error)) native
 rw [NNG_LegacyTerminal136.model] at old
 simp only [outer] at old
 unfold NNG_LegacySuffix136.f_r2
 dsimp only [NNG_LegacyConfig136.boundaries,NNG_LegacyConfig136.parent]
 rw [old,bind_tc_ok]
 exact success_r3 env s running alpha transcript1 val1 reply out tail
#print axioms success_r2
'''
s+=theorem('r1')+''' unfold NNG_SourceSuffixes.f_r1 at returned
 obtain ⟨reply,native,tail⟩ := bind_out _ _ _ returned
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok claims=>
   change NNG_SourceSuffixes.f_r2 (NNG_ConcreteCalls136.calls env) s running alpha transcript1 claims=.ok (.Ok out) at tail
   have old := congrArg (outer (NMP_ResultTransport.inner NNG_InstallClaims.lowerClaims toT13)) native
   change outer (NMP_ResultTransport.inner NNG_InstallClaims.lowerClaims toT13) (NNG_LIBClaims.call env s.prefixValue)=_ at old
   rw [NNG_LegacyCalls136.claims] at old
   simp only [outer,NMP_ResultTransport.inner] at old
   unfold NNG_LegacySuffix136.f_r1
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_r2 env s running alpha transcript1 claims out tail
#print axioms success_r1
'''
s+=theorem('mark2')+''' change NNG_SourceSuffixes.f_r1 (NNG_ConcreteCalls136.calls env) s running alpha transcript1=.ok (.Ok out) at returned
 unfold NNG_LegacySuffix136.f_mark2
 dsimp only [NNG_LegacyConfig136.parent]
 rw [LIB_Mark.result,bind_tc_ok]
 exact success_r1 env s running alpha transcript1 out returned
#print axioms success_mark2
'''
s+=theorem('r')+''' unfold NNG_SourceSuffixes.f_r at returned
 obtain ⟨reply,native,tail⟩ := bind_out _ _ _ returned
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok triple=>
   rcases triple with ⟨running,alpha,t1⟩
   change NNG_SourceSuffixes.f_mark2 (NNG_ConcreteCalls136.calls env) s running alpha t1=.ok (.Ok out) at tail
   have old := congrArg (outer (NMP_ResultTransport.inner NNG_Model134.lowerReply toT13)) native
   change outer (NMP_ResultTransport.inner NNG_Model134.lowerReply toT13) (NNG_Model134.rounds s.digest s.prefixValue s.transcript)=_ at old
   rw [NNG_LegacyCalls136.rounds] at old
   simp only [outer,NMP_ResultTransport.inner,NNG_Model134.lowerReply] at old
   unfold NNG_LegacySuffix136.f_r
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_mark2 env s running alpha t1 out tail
#print axioms success_r

theorem finish {H W : Type} (env : RSL.Env) (s : Parent H W) (out : r1_semantic.Verified H)
 (returned : NNG_Emitted.emitted (NNG_ConcreteCalls136.calls env) s=.ok (.Ok out)) :
 AspisR1PublicPreparation.FinishModel.finish AspisS1ExtractedRoundChildren.children
   (NNG_LegacyConfig136.boundaries env) (NNG_Install.digest s.digest) (toT9 s.publicValue)
   (toT12 s.prefixValue) (toT10 s.transcript) (toT3 s.challenges) none=.ok (.Ok (toT11 out)) := by
 have source : NNG_SourceSuffixes.f_r (NNG_ConcreteCalls136.calls env) s=.ok (.Ok out) := by
   rw [NNG_TreeEmission.source_suffixes]
   exact returned
 have model := success_r env s out source
 rw [NNG_LegacySuffix136.source] at model
 exact model
#print axioms finish
end AspisR1.NNG_ModelSuccess136
'''
(E/'NNG_ModelHead136.lean').write_text(s)
