from pathlib import Path
import json,hashlib,tarfile
w=Path('/home/dombarker/project-offloads/aspis-r1-j1a-adapter-public-adapted-20261016');o=w/'bindings-evidence';o.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def dump(p,d):p.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
files={}
def add(p,n):
 assert p.is_file() and not p.is_symlink(),p
 files[n]=p
run=w/'runs/bindings-a'
for p in run.rglob('*'):
 if p.is_file() and not p.is_symlink() and 'artifacts' not in p.parts and 'import-overlay' not in p.parts and p.name!='external-inputs.json':add(p,'run/'+str(p.relative_to(run)))
for folder in ['sources','successful-targets']:
 for p in (w/folder).rglob('*'):
  if p.is_file():add(p,folder+'/'+str(p.relative_to(w/folder)))
for name in ['runner.py','stage-bindings.py','staging-failure.json','external-inputs-public.json','input-manifests/before-bindings.json']:
 add(w/name,name)
r=read(w/'successful-targets/ExtractedAdapterWithdrawalBindings.json')
assert r['exit_status']==0 and r['axioms']['passed'] and len(r['axioms']['reports'])==2
assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
assert r['key']['source_sha256']==sha(w/'sources/ExtractedAdapterWithdrawalBindings.lean')
for v in r['objects'].values():
 assert sha(Path(v['path']))==v['sha256'];add(Path(v['path']),'final-artifacts/'+Path(v['path']).name)
for p in (w/'successful-targets').glob('*.json'):
 d=read(p)
 for v in d['objects'].values():assert sha(Path(v['path']))==v['sha256']
summary={k:r[k] for k in ['target','exit_status','wall_seconds','sampled_cgroup_peak_bytes','peak_process_rss_kib','process_swaps','cgroup_swap_current','axioms','objects']}
summary.update({'source_sha256':r['key']['source_sha256'],'revision':'2405d1deba8d61a0410503e9df77b3fe397ebd44 plus new binding theorem','limits':{'MemoryHigh':6*2**30,'MemoryMax':8*2**30,'MemorySwapMax':0},'scope':'Actual terminal-validator prefix and successful reconstruction bind fixed withdrawal fields to the supplied structural account records. No account authentication, custody, serializer-success or cross-stage checkpoint claim.','predecessors':'Existing four Adapter targets reused by exact receipts; earlier 2405d1d bundle supplies their producing checks. No predecessor replay.','preflight_failure':'Missing metadata directory during staging; before Lean, source/object unchanged; retained staging-failure.json.'})
dump(o/'check-summary.json',summary);add(o/'check-summary.json','check-summary.json');add(Path(__file__),'collect-bindings.py')
dump(o/'archive-members.json',{n:{'sha256':sha(p),'bytes':p.stat().st_size} for n,p in sorted(files.items())})
with tarfile.open(o/'adapter-bindings-evidence.tar.gz','w:gz') as t:
 for n,p in sorted(files.items()):t.add(p,arcname=n,recursive=False)
dump(o/'archive-pin.json',{'sha256':sha(o/'adapter-bindings-evidence.tar.gz'),'bytes':(o/'adapter-bindings-evidence.tar.gz').stat().st_size,'members':len(files)})
print((o/'archive-pin.json').read_text())
