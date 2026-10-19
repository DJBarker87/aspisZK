#!/usr/bin/env python3
"""Package existing caller checks, including the failed local proof attempt."""
from pathlib import Path
import hashlib,json,tarfile
W=Path('/home/dombarker/project-offloads/aspis-r1-j1a-caller-proof-20261016')
O=W/'evidence';O.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rd(p):return json.loads(p.read_text())
def wr(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
manifest=rd(W/'sources/SOURCE-MANIFEST.json');rows=[]
for n,m in manifest['modules'].items():assert sha(W/'sources'/m['stage_as'])==m['source_sha256']
for run in ['caller-a','caller-b']:
 for p in sorted((W/'runs'/run).glob('*/receipt.json')):
  r=rd(p);assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
  rows.append({'run':run,**{k:r[k] for k in ['target','exit_status','wall_seconds','peak_process_rss_kib','sampled_cgroup_peak_bytes','process_swaps','cgroup_swap_current','axioms']}})
for p in (W/'successful-targets').glob('*.json'):
 r=rd(p);assert r['exit_status']==0 and r['axioms']['passed']
 for v in r['objects'].values():assert sha(Path(v['path']))==v['sha256']
final=rd(W/'successful-targets/ExtractedWithdrawalCallerSuccess.json')
assert len(final['axioms']['reports'])==4
summary={'scope':'Actual extracted ASWP encoder first-bind inversion on the identical public value; no verifier/ASF8 reachability claim. Exact source errors preserved.',
 'source_revision':'173c8fe96 generated mirrors; owned proof based on8d89ba0da36be21149b48baf754cf938465569db, exact source SHA in manifest',
 'source_manifest_sha256':sha(W/'sources/SOURCE-MANIFEST.json'),
 'limits':{'MemoryHigh':6*2**30,'MemoryMax':8*2**30,'MemorySwapMax':0,'lean':['-j1','-M0']},
 'attempts':rows,'final':{'source_sha256':final['key']['source_sha256'],'objects':final['objects'],'axioms':final['axioms']},
 'failure':'caller-a optional exact-error theorem left core.convert.FromSame.from folded; required success inversion already had standard-only report. caller-b changes only the two local simp names and reuses generated2.',
 'unproved':['verifier/ASF8 caller reachability','ASWP returned-byte format/totality','transport to separately extracted validator carrier','correctness of Rust extraction tools']}
wr(O/'check-summary.json',summary)
files={}
def add(p,n=None):
 assert p.is_file() and not p.is_symlink(),p
 files[n or str(p.relative_to(W))]=p
for d in ['sources','successful-targets']:
 for p in (W/d).rglob('*'):
  if p.is_file():add(p)
for run in ['caller-a','caller-b']:
 for p in (W/'runs'/run).rglob('*'):
  if p.is_file() and not p.is_symlink() and 'import-overlay' not in p.parts and 'artifacts' not in p.parts and p.name!='external-inputs.json':add(p)
for p in (W/'runs/caller-b/ExtractedWithdrawalCallerSuccess/artifacts').rglob('*'):
 if p.is_file():add(p)
add(Path('/home/dombarker/project-offloads/aspis-r1-j17-port-20261015/extracted/external-inputs-002.json'),'external-inputs-002.json')
add(W/'runner.py');add(Path(__file__));add(O/'check-summary.json','check-summary.json')
wr(O/'archive-members.json',{n:{'sha256':sha(p),'bytes':p.stat().st_size} for n,p in sorted(files.items())})
with tarfile.open(O/'caller-check-evidence.tar.gz','w:gz') as t:
 for n,p in sorted(files.items()):t.add(p,arcname=n,recursive=False)
wr(O/'archive-pin.json',{'sha256':sha(O/'caller-check-evidence.tar.gz'),'bytes':(O/'caller-check-evidence.tar.gz').stat().st_size,'members':len(files)})
print((O/'archive-pin.json').read_text())
