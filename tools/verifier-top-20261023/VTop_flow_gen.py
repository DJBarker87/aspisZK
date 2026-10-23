from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean';s=(L/'VTop_Model.lean').read_text()
block=s.split('structure Ops where\n',1)[1].split('\n\n/--',1)[0]
fields=re.findall(r'  (op\d+|unwrap32) : (.*?)(?=\n  (?:op\d+|unwrap32) :|\Z)',block,re.S)
constructors=(L/'VTop_Trace.lean').read_text().split('inductive Call : Type → Type 1 where\n')[1].split('\ndef invoke',1)[0]
ported=[];source=[];traced=[]
for name,typ in fields:
 typ=' '.join(typ.split());depth=0;idx=[]
 for i,c in enumerate(typ):
  if c in '({[':depth+=1
  if c in ')}]':depth-=1
  if depth==0 and typ.startswith('Result ',i):idx.append(i)
 assert idx,(name,idx)
 i=idx[-1];ported.append('  '+name+' : '+typ[:i]+'M '+typ[i+7:]);source.append(f'  {name} := ops.{name}')
 line=next(l.strip() for l in constructors.splitlines() if l.strip().startswith('| '+name+' '));binders=line.split(' : Call ',1)[0].split(name,1)[1].strip();depth=0;ns=[]
 for i,c in enumerate(binders):
  if c in '({[':
   if depth==0:
    m=re.match(r'[({]([A-Za-z_][A-Za-z_0-9]*)\s*:',binders[i:]);assert m,(name,binders[i:]);ns.append((c,m[1]))
   depth+=1
  if c in ')}]':depth-=1
 pattern=' '.join('{'+n+'}' if c=='{' else n for c,n in ns);values=' '.join('('+n+' := '+n+')' if c=='{' else n for c,n in ns)
 traced.append(f'  {name} := '+(f'fun {pattern} => ' if ns else '')+f'perform (.{name} {values})')
header='''import VTop_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Flow
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace
universe v
structure Effects (M : Type → Type v) where
'''
out=header+'\n'.join(ported)+'\n\ndef sourceEffects (ops : Ops) : Effects Result := {\n'+'\n'.join(source)+'\n}\n\ndef traceEffects : Effects Code := {\n'+'\n'.join(traced)+'\n}\n\n'
for n in ['tx1','tx2_common','tx2_authenticated']:
 old='verifier.candidate.'+n;start=s.index('def '+old+' (ops : Ops)');end=s.find('\n/--',start)
 if end<0:end=s.index('\nend VTop_Stages',start)
 body=s[start:end].strip();body=body.replace('def '+old+' (ops : Ops)',f'def {n} {{M : Type → Type v}} [Monad M] [MonadLiftT Result M] (effects : Effects M)');body=re.sub(r'\n  Result ', '\n  M ',body,count=1);body=re.sub(r'\bok\b','pure',body);body=re.sub(r'(?<![A-Za-z0-9_.])ops\.', 'effects.',body).replace('(verifier.candidate.tx2_common ops)','(tx2_common effects)')
 out+=body+'\n\n'
out+='end AspisR1.VTop_Flow\nend\n'
(L/'VTop_Flow.lean').write_text(out)
