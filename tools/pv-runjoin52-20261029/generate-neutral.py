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
rawtower='PV_RunJoin_CircleRawTower52'
def neutral(d):
 d=d.replace('aspis_core.field.', 'field.')
 d=re.sub(r'\{ a, b \}', '{ fst := a, snd := b }',d)
 d=re.sub(r'\{ c0 := c, c1 \}', '{ fst := c, snd := c1 }',d)
 for a,b in [('a','fst'),('b','snd'),('c0','fst'),('c1','snd')]:
  d=re.sub(r'\.'+a+r'\b','.'+b,d)
  d=re.sub(r'\b'+a+r'\s*:=',b+' :=',d)
 return d
body='abbrev field.CM31 := U32 × U32\nabbrev field.QM31 := field.CM31 × field.CM31\n'
body+='\n'.join('abbrev '+n.replace('aspis_core.','')+' := '+raw+'.'+n.replace('aspis_core.','') for n in scalar)+'\n'
body+='\n\n'.join(neutral(defs[n]) for n in tower)
write(rawtower,['R1Z.'+raw],body,[n.replace('aspis_core.','') for n in tower])
carrier='''abbrev CM := U32 × U32
abbrev Q := CM × CM
abbrev Point := Q × Q
abbrev OC := PV_AL_CircleOwned.aspis_core.field.CM31
abbrev OQ := PV_AL_CircleOwned.aspis_core.field.QM31
abbrev OP := PV_AL_CircleOwned.aspis_core.circle.SecureCirclePoint
def encCM (a : CM) : OC := ⟨a.1,a.2⟩
def decCM (a : OC) : CM := (a.a,a.b)
def encQ (a : Q) : OQ := ⟨encCM a.1,encCM a.2⟩
def decQ (a : OQ) : Q := (decCM a.c0,decCM a.c1)
def encPoint (a : Point) : OP := ⟨encQ a.1,encQ a.2⟩
def decPoint (a : OP) : Point := (decQ a.x,decQ a.y)
theorem cm_roundtrip (a : CM) : decCM (encCM a)=a := rfl
theorem q_roundtrip (a : Q) : decQ (encQ a)=a := rfl
theorem point_roundtrip (a : Point) : decPoint (encPoint a)=a := rfl
theorem cm_source (a : OC) : encCM (decCM a)=a := rfl
theorem q_source (a : OQ) : encQ (decQ a)=a := rfl
theorem point_source (a : OP) : encPoint (decPoint a)=a := rfl
'''
write('PV_RunJoin_CircleOwnedCarrier52',['R1Z.PV_AL_CircleOwnedTypes'],carrier,['encCM','decCM','encQ','decQ','encPoint','decPoint','cm_roundtrip','q_roundtrip','point_roundtrip','cm_source','q_source','point_source'])
# One named declaration per primitive, with carrier conversion only at its boundary.
body='open PV_RunJoin_CircleOwnedCarrier52\n'
proofs=[]
for i,n in enumerate(tower):
 d=defs[n]; sig=d[:d.index(':=')];sig=sig.replace('def '+n,'')
 sep=sig.rfind(':');binder=sig[:sep].strip();result=sig[sep+1:].strip()
 # scalar function inverse binder is intentionally kept on standard U32
 binder=binder.replace('aspis_core.field.M31','U32').replace('aspis_core.field.CM31','CM').replace('aspis_core.field.QM31','Q')
 args=re.findall(r'\((\w+)\s*:',binder)
 # extract each argument's type for the encoder
 call=[]
 for a in args:
  typ=re.search(r'\('+a+r'\s*:\s*([^\)]+)\)',binder)[1]
  call.append(f'(encCM {a})' if typ=='CM' else f'(encQ {a})' if typ=='Q' else a)
 rawname=n.replace('aspis_core.','')
 const=not result.startswith('Result')
 out=result.replace('Result','').strip()
 encoder='encCM' if out=='aspis_core.field.CM31' else 'encQ' if out=='aspis_core.field.QM31' else None
 if out.startswith('(') and 'Option' in out: encoder='(Option.map encQ)'
 if out=='Bool': encoder=None
 rhs=rawtower+'.'+rawname+' '+' '.join(args)
 if encoder:rhs=(encoder+' ('+rhs+')') if const else '(do let x ← '+rhs+'; ok ('+encoder+' x))'
 stmt=f'theorem t{i} {binder} :\n    PV_AL_CircleOwned.{n} '+ ' '.join(call)+' = '+rhs+' := by\n'
 deps=[f't{j}' for j in range(i) if tower[j] in d[len('def '+n):]]
 deps+=['PV_RunJoin_CircleOwnedScalar52.f'+str(j) for j in range(len(scalar)) if scalar[j] in d[len('def '+n):]]
 stmt+='  unfold PV_AL_CircleOwned.'+n+' '+rawtower+'.'+rawname+'\n'
 stmt+='  simp only ['+','.join(deps+['bind_assoc_eq','bind_tc_ok','encCM','encQ'])+']\n'
 body+=stmt+'\n';proofs.append('t'+str(i))
write('PV_RunJoin_CircleOwnedTower52',['R1Z.PV_RunJoin_CircleOwnedScalar52','R1Z.PV_RunJoin_CircleOwnedCarrier52','R1Z.'+rawtower],body,proofs)
