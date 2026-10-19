from pathlib import Path
import json,hashlib,tarfile
B=Path('/home/dombarker/project-offloads')
W=B/'aspis-r1-j1a-caller-adapted-20261016';O=W/'evidence';O.mkdir(exist_ok=True)
P=B/'aspis-r1-j1a-caller-proof-20261016';J=B/'aspis-r1-j1a-caller-joint-20261016'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rd(p):return json.loads(p.read_text())
def wr(p,d):p.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
files={};rows=[]
def add(p,n):
 assert p.is_file() and not p.is_symlink(),p
 files[n]=p
for label,w,runs in [('adapted',W,['adapter-a','adapter-b','adapter-c']),('original',P,['discriminant-original-a']),('joint',J,['joint-a'])]:
 for run in runs:
  for p in (w/'runs'/run).rglob('*'):
   if p.is_file() and not p.is_symlink() and 'artifacts' not in p.parts and 'import-overlay' not in p.parts and p.name!='external-inputs.json':add(p,f'{label}/runs/{run}/'+str(p.relative_to(w/'runs'/run)))
  for p in (w/'runs'/run).glob('*/receipt.json'):
   d=rd(p);assert d['process_swaps']==0 and d['cgroup_swap_current']=='0';rows.append({'origin':label,'run':run,**{k:d[k] for k in ['target','exit_status','wall_seconds','sampled_cgroup_peak_bytes','peak_process_rss_kib','process_swaps','cgroup_swap_current','axioms']}})
 for p in (w/'input-manifests').glob('*.json') if (w/'input-manifests').exists() else []:add(p,f'{label}/input-manifests/'+p.name)
 for n in ['runner.py','stage.py','external-inputs-carrier.json','import-source-audit.json']:
  if (w/n).exists():add(w/n,f'{label}/'+n)
for p in (W/'sources').rglob('*'):
 if p.is_file():add(p,'adapted/sources/'+str(p.relative_to(W/'sources')))
for p in (W/'successful-targets').glob('*.json'):
 r=rd(p);assert r['exit_status']==0 and r['axioms']['passed']
 for v in r['objects'].values():assert sha(Path(v['path']))==v['sha256']
 add(p,'adapted/successful-targets/'+p.name)
a=P/'runs/discriminant-original-a/WithdrawalCallerDiscriminantAudit/lean.log';b=W/'runs/adapter-a/WithdrawalCallerDiscriminantAudit/lean.log';assert a.read_bytes()==b.read_bytes()
final=rd(W/'successful-targets/ExtractedWithdrawalCallerCarrier.json');assert final['key']['source_sha256']==sha(W/'sources/ExtractedWithdrawalCallerCarrier.lean');assert len(final['axioms']['reports'])==8
summary={'scope':'Actual ASWP first-validator success, transported through fixed all-nine-field maps and all14 error constructors to existing WithdrawalCarrier431.HelperValidated; no terminal/verifier reachability claim.',
 'final_source_sha256':final['key']['source_sha256'],'final_objects':final['objects'],'final_axioms':final['axioms'],'attempts':rows,
 'naming_adapter':'Only Caller Error discriminant attribute expanded to identical read_discriminant and qualified instance; original generated mirrors/cache remain intact.',
 'discriminant_logs_identical':True,'discriminant_log_sha256':sha(a),'predecessor_manifest_mapping_note':'Initial adapted receipt source_manifest_entry canonical source labels used shorthand lean/Types.lean and lean/Funs.lean; final SOURCE-MANIFEST gives correct bridge/extracted paths. Exact staged bytes and object/import/runtime keys were unchanged; no claim of a file at the shorthand canonical path.',
 'limits':{'MemoryHigh':6*2**30,'MemoryMax':8*2**30,'MemorySwapMax':0},
 'remaining':['actual terminal/verifier reachability','Terminal namespace transport','extraction-tool correctness','ASWP encoder returned-byte format and totality']}
wr(O/'check-summary.json',summary);add(O/'check-summary.json','check-summary.json');add(Path(__file__),'collect.py')
add(P/'runs/discriminant-original-a/external-inputs.json','original/external-inputs.json')
wr(O/'archive-members.json',{n:{'sha256':sha(p),'bytes':p.stat().st_size} for n,p in sorted(files.items())})
with tarfile.open(O/'carrier-check-evidence.tar.gz','w:gz') as t:
 for n,p in sorted(files.items()):t.add(p,arcname=n,recursive=False)
wr(O/'archive-pin.json',{'sha256':sha(O/'carrier-check-evidence.tar.gz'),'bytes':(O/'carrier-check-evidence.tar.gz').stat().st_size,'members':len(files)})
print((O/'archive-pin.json').read_text())
