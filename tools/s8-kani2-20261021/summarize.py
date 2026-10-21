#!/usr/bin/env python3
"""Validate the focused continuation packet, without replaying any solver."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s8-kani2-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[];accepted={}
for p in sorted((E/'proofs').glob('*/receipt.json')):
 d=json.loads(p.read_text());d['receipt']=str(p.relative_to(E))
 for key in ['module','command','source_sha256','source_revision','deps_fingerprint','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']:assert key in d,(p,key)
 assert sha(p.with_name('source.lean'))==d['source_sha256']
 assert d['swaps']==0
 if d['exit_status']==0:
  assert 'sorryAx' not in p.with_name('lean.log').read_text(),p
  for line in d['print_axioms']:
   if 'depends on axioms:' in line:
    names=set(re.findall(r'\b[A-Za-z][A-Za-z_.]*\b',line.split('depends on axioms:')[1]))
    assert names<={'propext','Classical.choice','Quot.sound'},(p,names)
  source=B/'lean'/(d['module'].replace('.','/')+'.lean')
  if sha(source)==d['source_sha256']:accepted[d['module']]=d
 records.append(d)
for source in sorted((B/'lean').glob('S8Kani2*.lean')):
 assert source.stem in accepted,source
 text=source.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b',text),source
 assert not re.search(r'^\s*(axiom\s|set_option\s+(maxRecDepth|maxHeartbeats))',text,re.M),source
 theorem_names=re.findall(r'^(?:private )?theorem\s+(\w+)',text,re.M)
 for theorem in theorem_names:assert '#print axioms '+theorem in text,(source,theorem)
 assert len(accepted[source.stem]['print_axioms'])>=len(theorem_names),source
host=[]
for p in sorted((E/'receipts').glob('*/receipt.json')):
 d=json.loads(p.read_text());d['receipt']=str(p.relative_to(E))
 for key in ['target','source_revision','source_sha256','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']:assert key in d,(p,key)
 assert d['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert d['swaps']==0 and d['cgroup_swap_peak_bytes']==0
 host.append(d)
assert next(d for d in host if d['attempt']=='kani2-04')['exit_status']==0
assert next(d for d in host if d['attempt']=='kani2-05')['exit_status']==124
assert next(d for d in host if d['attempt']=='kani2-06')['exit_status']==0
base='6ecb5fc09'
headline='docs/research/100bit-spend-path-20261013/lean/R1FinalSoundnessBinPerQueryR19.lean'
original=subprocess.check_output(['git','show',base+':'+headline],cwd=R)
assert (R/headline).read_bytes()==original
changed=subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs'],cwd=R,text=True).splitlines();assert not changed,changed
status=dict(schema='focused-extractor-proof-packet-v1',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),accepted_modules=sorted(accepted),accepted_theorem_audits=sum(len(d['print_axioms']) for d in accepted.values()),lean_attempts=len(records),host_attempts=len(host),lean_peak_rss_bytes=max(d['peak_rss_bytes'] for d in accepted.values()),host_cgroup_peak_bytes=max(d['cgroup_memory_peak_bytes'] for d in host),swaps=0,headline_sha256=sha(R/headline),headline_signature_change='none; no premise removed',frozen_whole_loop_rerun=False,global_S8='OPEN: production caller congruence/checkpoint provenance and interpretation of free boundary S8',rust_to_model_scope='P6 one-step at capacity 64; selected raw read factored and supplied by Lean value_reference; opaque Aeneas IterMut model is not an extracted proof of Rust unsafe stdlib')
(E/'manifest.json').write_text(json.dumps(dict(**status,lean_attempt_records=records,host_attempt_records=host),indent=2)+'\n')
(E/'accepted-summary.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps(status,indent=2))
