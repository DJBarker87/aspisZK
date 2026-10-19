from pathlib import Path
import json,hashlib,tarfile
B=Path('/home/dombarker/project-offloads');W=B/'aspis-r1-j1a-terminal-caller-adapted-20261016';J=B/'aspis-r1-j1a-terminal-caller-joint-20261016';O=W/'evidence';O.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rd(p):return json.loads(p.read_text())
def wr(p,d):p.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
files={};rows=[]
def add(p,n):
 assert p.is_file() and not p.is_symlink(),p
 files[n]=p
for label,w in [('adapted',W),('joint',J)]:
 for run in sorted((w/'runs').iterdir()):
  for p in run.rglob('*'):
   if p.is_file() and not p.is_symlink() and 'artifacts' not in p.parts and 'import-overlay' not in p.parts and p.name!='external-inputs.json':add(p,f'{label}/runs/{run.name}/'+str(p.relative_to(run)))
  for p in run.glob('*/receipt.json'):
   d=rd(p);assert d['process_swaps']==0 and d['cgroup_swap_current']=='0';rows.append({'origin':label,'run':run.name,**{k:d[k] for k in ['target','exit_status','wall_seconds','sampled_cgroup_peak_bytes','peak_process_rss_kib','process_swaps','cgroup_swap_current','axioms']}})
 for folder in ['sources','successful-targets','input-manifests']:
  for p in (w/folder).rglob('*') if (w/folder).exists() else []:
   if p.is_file():add(p,f'{label}/{folder}/'+str(p.relative_to(w/folder)))
 for n in ['runner.py','stage-joint.py','stage-adapted.py','external-inputs-carrier.json','external-inputs-terminal.json','import-source-audit.json','removed-original-caller-pins.json','tooling-launch-note.json']:
  if (w/n).exists():add(w/n,f'{label}/'+n)
for p in (W/'successful-targets').glob('*.json'):
 r=rd(p);assert r['exit_status']==0 and r['axioms']['passed']
 for v in r['objects'].values():assert sha(Path(v['path']))==v['sha256']
a=J/'runs/kind-original-a/WithdrawalCallerKindAudit/lean.log';b=W/'runs/adapter-a/WithdrawalCallerKindAudit/lean.log';assert a.read_bytes()==b.read_bytes()
final=rd(W/'successful-targets/ExtractedTerminalCallerBridge.json');assert final['key']['source_sha256']==sha(W/'sources/ExtractedTerminalCallerBridge.lean');assert len(final['axioms']['reports'])==10
for v in final['objects'].values():
 add(Path(v['path']),'final-artifacts/'+Path(v['path']).name)
summary={'scope':'Fixed all-nine-field Terminal-to-Caller carrier, actual complete validator/ASWP encoder outcome equality, and terminal withdrawal validation success implies standalone actual ASWP encoder success with unchanged bytes.',
'final_source_sha256':final['key']['source_sha256'],'final_objects':final['objects'],'final_axioms':final['axioms'],'attempts':rows,
'naming_adapter':'Only Caller Kind discriminant attribute expanded to identical two-code read_discriminant and qualified instance; existing fourteen-code Error expansion unchanged; original emitted sources/caches and Terminal generated files untouched.',
'kind_discriminant_logs_identical':True,'kind_discriminant_log_sha256':sha(a),
'limits':{'MemoryHigh':6*2**30,'MemoryMax':8*2**30,'MemorySwapMax':0},
'remaining':['admitted verifier reaches this actual terminal validator','semantic public serializer success and supplied public equality','account/omitted-metadata binding beyond exposed terminal checks','joint import with retained public/Validation namespace needs its own naming compatibility check','extraction-tool correctness']}
wr(O/'check-summary.json',summary);add(O/'check-summary.json','check-summary.json');add(Path(__file__),'collect.py')
wr(O/'archive-members.json',{n:{'sha256':sha(p),'bytes':p.stat().st_size} for n,p in sorted(files.items())})
with tarfile.open(O/'terminal-caller-evidence.tar.gz','w:gz') as t:
 for n,p in sorted(files.items()):t.add(p,arcname=n,recursive=False)
wr(O/'archive-pin.json',{'sha256':sha(O/'terminal-caller-evidence.tar.gz'),'bytes':(O/'terminal-caller-evidence.tar.gz').stat().st_size,'members':len(files)})
print((O/'archive-pin.json').read_text())
