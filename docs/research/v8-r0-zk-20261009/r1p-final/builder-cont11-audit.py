#!/usr/bin/env python3
"""Read-only source/dependency/axioms and projected Kani receipt audit."""
from pathlib import Path
import hashlib, json, re, subprocess
H=Path(__file__).resolve().parent
ROOT=H.parents[3]
def sha(b): return hashlib.sha256(b).hexdigest()
records=[json.loads(x) for x in (H/'builder-cont11-attempts.jsonl').read_text().splitlines()]
accepted=[r for r in records if r['exit']==0]
assert len(accepted)==3 and len(records)==4
script='''from pathlib import Path
import hashlib,json,re
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
R=Path('/home/dombarker/project-offloads/codex-cx-builder-ref11-20261021')
def pin(p):return dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size)
envpath=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
env=json.loads(envpath.read_text())
result={'modules':{},'kani':{},'environment':pin(envpath),'lean':pin(Path(env['LEAN'])),'launcher':pin(R/'run-joint.sh')}
for m in ['BuilderForestCallbackAdapter','BuilderForestAdmissionPort','BuilderForestAdmissionProgress']:
 p=J/'sources/R1Z'/f'{m}.lean';imports=re.findall(r'^import (\\S+)',p.read_text(),re.M)
 deps={}
 for x in imports:
  suffix=x.replace('.','/')+'.olean'
  choices=[J/'objects'/suffix]+[Path(z)/suffix for z in env['LEAN_PATH'].split(':')]
  deps[x]=pin(next(z for z in choices if z.exists()))
 def direct_sha(x):
  p=J/'objects'/(x.replace('.','/')+'.olean')
  return pin(p)['sha256'] if p.exists() else 'missing'
 fp=hashlib.sha256(';'.join(f'{x}={direct_sha(x)}' for x in sorted(imports)).encode()).hexdigest()[:16]
 result['modules'][m]=dict(source=pin(p),object=pin(J/'objects/R1Z'/f'{m}.olean'),dependencies=deps,deps_fingerprint=fp)
for p in (R/'iterator-step').glob('*/receipt.json'):
 d=p.parent;n=d.name
 result['kani'][n]=dict(receipt=json.loads(p.read_text()),logs={x:(d/x).read_text() for x in ['stdout.log','stderr.log','time.log']},sources=json.loads((d.parent/(n+'-sources.json')).read_text()),reservation=json.loads((d.parent/(n+'-reservation.json')).read_text()))
print(json.dumps(result))
'''
d=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=script,text=True))
for r in accepted:
 m=r['module'].split('.')[-1]; p=ROOT/r['repo_source'];assert sha(p.read_bytes())==r['source_sha256']==d['modules'][m]['source']['sha256']
 assert r['deps_fingerprint']==d['modules'][m]['deps_fingerprint']
 assert r['swaps']=='0'
 for a in r['axioms']:
  v=re.search(r'depends on axioms: \[([^\]]*)\]',a)
  if v:assert set(v.group(1).replace('\n','').replace(' ','').split(','))<= {'propext','Classical.choice','Quot.sound'},a
 assert not re.search(r'\b(sorryAx|declaration uses `sorry`)\b',r['stdout'])
for name,k in d['kani'].items():
 assert k['receipt']['exit_status']==0 and k['receipt']['swaps']==0
 assert k['receipt']['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert 'VERIFICATION:- SUCCESSFUL' in k['logs']['stdout.log']
 for f,pin in k['sources'].items():
  p=ROOT/f; data=p.read_bytes()
  if name=='trace_drop_iterator_step' and f.endswith('/drop_iterator.rs'):
   data=data[:data.index(b'/// The outer loop')]
   # The recorded version ends before the blank line introducing the outer harness.
   data=data.rstrip()+b'\n'
  assert sha(data)==pin['sha256'],(name,f)
 d['kani'][name]['scope']='Projected actual std iterator/pointer step, not whole shipped Drop; P6 tool soundness remains named'
# The source file changed solely by appending the outer harness after the first run.
assert len(d['kani'])==2
changed=subprocess.check_output(['git','diff','--name-only','4715dbaf3','--','crates','programs'],cwd=ROOT,text=True).splitlines()
assert not changed,changed
d.update(accepted_attempts=[r['attempt'] for r in accepted],failed_attempts=[r['attempt'] for r in records if r['exit']!=0],axioms_count=sum(len(r['axioms']) for r in accepted),shipped_changes=changed,elf_rule='not triggered: no shipped crate/program source changed',remaining_attempts=[],status='Focused proofs only; no full semantic admission, destructor source identification or privacy-premise deletion claimed')
(H/'builder-cont11-audit.json').write_text(json.dumps(d,indent=2)+'\n')
print('PASS',len(accepted),'modules;',d['axioms_count'],'axioms audits;',len(d['kani']),'projected Kani receipts; no shipped changes')
