"""Reify only the exact digest calls in retained materialization source.
All other Result operations are lifted unchanged. --check never launches.
"""
from pathlib import Path
import re,hashlib,json,sys
r=Path(__file__).resolve().parents[3];p=r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean';s=p.read_text();a=s.index('def host_transcript.Transcript.absorb');b=s.index('\n/--',a);absorb=s[a:b]
p2=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwQueryMaterial.lean';s2=p2.read_text();a=s2.index('def materializeK');b=s2.index('\n\ndef materialize ',a);material=s2[a:b]
def transform(t):
 t=t.replace('Result (host_transcript.Transcript H)','Execution (host_transcript.Transcript H)').replace('Result α','Execution α')
 t=t.replace('def host_transcript.Transcript.absorb','def absorb')
 pos=t.index(':= do');head=t[:pos+5];body=t[pos+5:]
 chunks=re.split(r'(?m)(?=^  let |^  ok |^  k )',body)
 out=[]
 for chunk in chunks:
  if not chunk.strip():continue
  if ' ←' not in chunk:
   out.append(chunk.replace('  ok ','  ProverRwOrderedOracle.pure ',1));continue
  left,rhs=chunk.split('←',1);rhs=rhs.strip()
  if rhs.startswith('aspis_coredigestDigest32Inst.digest '):
   m=re.match(r'aspis_coredigestDigest32Inst.digest (\S+) (\S+)\s*$',rhs);assert m,rhs
   value=f'query (aspis_coredigestDigest32Inst.digest {m[1]}) {m[2]}'
  elif rhs.startswith('host_transcript.Transcript.absorb '):value=rhs.replace('host_transcript.Transcript.absorb ','absorb ',1)
  else:value='native ('+rhs+')'
  out.append(left+'← '+value+'\n')
 return head+'\n'+''.join(out).rstrip()
t='''import R1Z.ProverRwOrderedOracle
import R1Z.ProverRwQueryMaterial
set_option autoImplicit false
namespace R1Z.ProverRwOrderedQuerySource
open Aeneas Aeneas.Std Result ProverRwFull ProverRwQueryScan
open ProverRwOrderedOracle
variable [ExternalTypes] [ExternalFuns]
'''+transform(absorb)+'\n\n'+transform(material)+'''

def materialize {H : Type} (hash : aspis_core.digest.Digest32 H)
    (self : host_transcript.Transcript H) (row : U8) (payload : Slice U8) :=
  materializeK hash self row payload (fun s b a => ProverRwOrderedOracle.pure (s,b,a))
end R1Z.ProverRwOrderedQuerySource
'''
o=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwOrderedQuerySource.lean'
if '--check' in sys.argv:assert o.read_text()==t
else:
 o.write_text(t)
 (r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-resume/ordered-query-source.json').write_text(json.dumps(dict(absorb_sha256=hashlib.sha256(absorb.encode()).hexdigest(),materialize_sha256=hashlib.sha256(material.encode()).hexdigest(),output_sha256=hashlib.sha256(t.encode()).hexdigest(),changes='Exactly17 digest method calls reified. Same arguments, native guards, Array callbacks, order and source continuations. Source trace instrumentation only; native ROM/TLS association remains open.'),indent=2)+'\n')
print(hashlib.sha256(t.encode()).hexdigest())
