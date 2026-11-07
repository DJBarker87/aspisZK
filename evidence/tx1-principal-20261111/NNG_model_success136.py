from pathlib import Path
import json
E=Path(__file__).resolve().parent
points={p['name']:p for p in json.loads((E/'NNG_SOURCE_OCCURRENCES.json').read_text())}
conv={n:'(toT1 '+n+')'for n in ['running','val2','q','mask','q1','q2','q3','masked_terminal']}
conv.update({n:'(arr toT1 '+n+')'for n in ['alpha','val3','val5','a','a1','a2']})
conv.update(val1='(NNG_InstallClaims.lowerClaims val1)',r2='(NMP_ResultTransport.inner toT1 NNG_LegacyTerminal136.error r2)')
conv.update({n:'(toT10 '+n+')'for n in ['transcript1','transcript2','transcript3']})
conv.update({n:'(toT2 '+n+')'for n in ['val4','val6']})
conv.update({n:'(toT14 '+n+')'for n in ['vr','vr1','vr2','vr3']})
conv.update({n:'(NMP_ResultTransport.inner toT14 toT13 '+n+')'for n in ['r4','r7']})
def theorem(name):
 p=points[name]
 return f'''theorem success_{name} {{H W : Type}} (env : RSL.Env) (s : Parent H W){p['args']}
 (out : r1_semantic.Verified H)
 (returned : NNG_SourceSuffixes.f_{name} (NNG_ConcreteCalls136.calls env) s {p['app']}=.ok (.Ok out)) :
 NNG_LegacySuffix136.f_{name} (NNG_LegacyConfig136.boundaries env) (NNG_LegacyConfig136.parent s)
  {' '.join(conv.get(n,n) for n in p['free'])}=.ok (.Ok (toT11 out)) := by
'''
header='''import NNG_LegacyCalls136
import NNG_SourceSuffixes
import NNG_TreeEmission
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ModelSuccess136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Transport
open NMP_ResultTransport (outer)
open NMT_Transport (arr)

theorem bind_out {A B : Type} (m : Result A) (f : A → Result B) (out : B)
 (run : (do let a←m;f a)=.ok out) : ∃ a,m=.ok a ∧ f a=.ok out := by
 cases m with
 | ok a=>exact ⟨a,rfl,run⟩
 | fail e=>cases run
 | div=>cases run
#print axioms bind_out
'''
s=header+theorem('a3')+''' cases r11 with
 | Err e=>
   simp only [NNG_SourceSuffixes.f_a3,core.result.Result.unwrap,bind_tc_fail] at returned
   cases returned
 | Ok root=>
   simp only [NNG_SourceSuffixes.f_a3,core.result.Result.unwrap,bind_tc_ok] at returned
   have same := core.result.Result.Ok.inj (Result.ok.inj returned)
   subst out
   simp only [NNG_LegacySuffix136.f_a3,NNG_LegacyConfig136.boundaries,core.result.Result.unwrap,bind_tc_ok,
    NNG_LegacyConfig136.parent,NNG_Transport.toT11,NMT_Transport.arr,List.map_cons,List.map_nil]
   rfl
#print axioms success_a3
'''+theorem('r11')+''' unfold NNG_SourceSuffixes.f_r11 at returned
 obtain ⟨reply,copy,tail⟩ := bind_out _ _ _ returned
 unfold NNG_LegacySuffix136.f_r11
 rw [copy,bind_tc_ok]
 exact success_a3 env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 reply out tail
#print axioms success_r11
'''+theorem('r10')+''' unfold NNG_SourceSuffixes.f_r10 at returned
 obtain ⟨reply,payload,tail⟩ := bind_out _ _ _ returned
 cases reply with
 | Err e=>
   change (.ok (.Err e) : Result (Output H))=.ok (.Ok out) at tail
   cases tail
 | Ok bytes=>
   change NNG_SourceSuffixes.f_r11 (NNG_ConcreteCalls136.calls env) s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 bytes=.ok (.Ok out) at tail
   have old := congrArg (outer (NMP_ResultTransport.inner id toT13)) payload
   change outer (NMP_ResultTransport.inner id toT13) (NNG_Install.payload s.prefixValue 2#u8)=_ at old
   rw [NNG_Install.payload_same] at old
   simp only [outer,NMP_ResultTransport.inner,id_eq] at old
   unfold NNG_LegacySuffix136.f_r10
   dsimp only [NNG_LegacyConfig136.parent]
   rw [old,bind_tc_ok]
   exact success_r11 env s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 bytes out tail
#print axioms success_r10
end AspisR1.NNG_ModelSuccess136
'''
(E/'NNG_ModelRoot136.lean').write_text(s)
