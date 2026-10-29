from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-runjoin52-20261029'
s=(L/'PV_AL_CircleOwnedFuns.lean').read_text()
s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
s=re.sub(r'@\[.*?\]\s*','',s,flags=re.S)
s=s[s.index('def aspis_core.field.P'):s.index('def shipped_sampler.qm31_div_pass_loop.body')]
parts=re.split(r'(?=^def )',s,flags=re.M);defs={re.match(r'def (\S+)',p)[1]:p.strip() for p in parts if p.strip()}
scalar=[];tower=[]
for n,d in defs.items():
 if n.startswith('aspis_core.field.CM31.') or n.startswith('aspis_core.field.QM31.') or n=='aspis_core.field.mul_by_r': tower.append(n)
 else: scalar.append(n)
# scalar sub/neg/is_zero are interleaved in the original; order below retains original dependencies.
def write(name,imports,body,prints):
 text='\n'.join('import '+i for i in imports)+'\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace R1Z.'+name+'\n'+body+'\n'+''.join('#print axioms '+n+'\n' for n in prints)+'end R1Z.'+name+'\n'
 (L/(name+'.lean')).write_text(text)
raw='PV_RunJoin_CircleRawScalar52'
body='\n\nabbrev field.M31 := U32\n\n'+'\n\n'.join(defs[n].replace('aspis_core.field.','field.') for n in scalar)
write(raw,['Aeneas','R1Z.PV_AL_ShiftLiterals'],body,[n.replace('aspis_core.','') for n in scalar])
# Every equation stays at the named function level. Never evaluate an exponentiation chain.
body='abbrev O := PV_AL_CircleOwned.aspis_core.field.M31\n'
body+='\n'
proofs=[]
for i,n in enumerate(scalar):
 d=defs[n]; sig=d[:d.index(':=')].replace('def '+n,'theorem f'+str(i)).replace('aspis_core.field.M31','O')
 # form binders, return type and arguments from the source signature
 binder=sig[sig.index('('):sig.rfind(':')] if '(' in sig else ''
 if not '(' in sig: binder=''
 args=re.findall(r'\((\w+)\s*:',binder)
 result=sig[sig.rfind(':')+1:].strip()
 # loop body and pair ControlFlow result contain colons only in binders; rightmost is result separator
 rawname=n.replace('aspis_core.','')
 app=' '.join(args)
 statement=f'theorem f{i} {binder}:\n    PV_AL_CircleOwned.{n} {app}= {raw}.{rawname} {app} := by\n'
 prev=[f'f{j}' for j in range(i) if scalar[j] in d[len('def '+n):]]
 statement+='  unfold PV_AL_CircleOwned.'+n+' '+raw+'.'+rawname+'\n'
 if prev: statement+='  simp only ['+','.join(prev)+']\n'
 if not prev: statement+='  rfl\n'
 body+=statement+'\n';proofs.append('f'+str(i))
write('PV_RunJoin_CircleOwnedScalar52',['R1Z.PV_AL_CircleOwnedFuns','R1Z.'+raw],body,proofs)
(E/'neutral-generation.json').write_text(json.dumps(dict(source_sha256=hashlib.sha256((L/'PV_AL_CircleOwnedFuns.lean').read_bytes()).hexdigest(),scalar_functions=scalar,tower_functions=tower,method='Proof-native neutral reification; original generated sources read-only; no authority substitution'),indent=2)+'\n')
