from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin52-20261029'
s=(L/'PV_AL_CircleOwnedFuns.lean').read_text();s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'@\[.*?\]\s*','',s,flags=re.S)
s=s[s.index('def shipped_sampler.qm31_div_pass_loop.body'):s.index('end PV_AL_CircleOwned')]
parts=[x.strip() for x in re.split(r'(?=^def )',s,flags=re.M) if x.strip()];defs={re.match(r'def (\S+)',x)[1]:x for x in parts}
def neutral(d):
 d=d.replace('aspis_core.field.', 'PV_RunJoin_CircleRawTower52.field.')
 d=d.replace('aspis_core.circle.SecureCirclePoint','Point').replace('aspis_core.circle.CirclePointError','Bool').replace('aspis_core.r0_transcript.CircleRow','Bool')
 d=d.replace('Bool.SingularParameter','false').replace('Bool.ParameterInCm31Subfield','true').replace('Bool.First','false').replace('Bool.Second','true')
 d=re.sub(r'\{ c0 := c, c1 \}', '{ fst := c, snd := c1 }',d)
 for a,b in [('a','fst'),('b','snd'),('c0','fst'),('c1','snd'),('x','fst'),('y','snd')]:
  d=re.sub(r'\.'+a+r'\b','.'+b,d);d=re.sub(r'\b'+a+r'\s*:=',b+' :=',d)
 return d
sampler={n:d for n,d in defs.items() if n.startswith('shipped_sampler.')}
raw='PV_RunJoin_CircleRawSampler52'
text='import R1Z.PV_RunJoin_CircleRawTower52\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace R1Z.'+raw+'\n'
text+='\n\n'.join(neutral(d) for d in sampler.values())+'\n'+''.join('#print axioms '+n+'\n' for n in sampler)+'end R1Z.'+raw+'\n'
(L/(raw+'.lean')).write_text(text)
body=''
for i,(n,d) in enumerate(sampler.items()):
 sig=d[:d.index(':=')].removeprefix('def '+n).strip();sep=sig.rfind(':');binder=sig[:sep].strip();result=sig[sep+1:].strip();args=re.findall(r'\((\w+)\s*:',binder)
 out=' '.join(args);rhs=raw+'.'+n+' '+out
 if n.endswith('qm31_sample'):rhs='(do let x ← '+rhs+'; ok (encQ x))'
 body+=f'theorem s{i} {binder} :\n    PV_AL_CircleOwned.{n} '+out+' = '+rhs+' := by\n'
 body+='  unfold PV_AL_CircleOwned.'+n+' '+raw+'.'+n+'\n'
 deps=['s'+str(j) for j,(m,_) in enumerate(list(sampler.items())[:i]) if m in d[len('def '+n):]]
 if 'aspis_core.field.P' in d: deps+=['PV_RunJoin_CircleOwnedScalar52.f0']
 if n.endswith('qm31_sample'):deps+=['PV_RunJoin_CircleOwnedOps52.op3','bind_assoc_eq','bind_tc_ok','encQ']
 if deps:body+='  simp only ['+','.join(deps)+']\n'
 body+='  all_goals rfl\n\n'
text='import R1Z.PV_RunJoin_CircleOwnedOp2152\nimport R1Z.'+raw+'\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace R1Z.PV_RunJoin_CircleOwnedSampler52\nopen PV_RunJoin_CircleOwnedCarrier52\n'+body+''.join('#print axioms s'+str(i)+'\n' for i in range(len(sampler)))+'end R1Z.PV_RunJoin_CircleOwnedSampler52\n'
(L/'PV_RunJoin_CircleOwnedSampler52.lean').write_text(text)
rawcircle='PV_RunJoin_CircleRawMap52';circle={n:d for n,d in defs.items() if not n.startswith('shipped_sampler.')}
text='import R1Z.'+raw+'\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace R1Z.'+rawcircle+'\nabbrev Q := PV_RunJoin_CircleRawTower52.field.QM31\nabbrev Point := Q × Q\nabbrev shipped_sampler.qm31_sample := '+raw+'.shipped_sampler.qm31_sample\n'
text+='\n\n'.join(neutral(d) for d in circle.values())+'\n'+''.join('#print axioms '+n+'\n' for n in circle)+'end R1Z.'+rawcircle+'\n'
(L/(rawcircle+'.lean')).write_text(text)
