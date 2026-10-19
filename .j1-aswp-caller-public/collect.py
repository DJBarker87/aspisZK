from pathlib import Path
import json,hashlib,tarfile
W=Path('/home/dombarker/project-offloads/aspis-r1-j1a-caller-public-20261016');O=W/'evidence';O.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rd(p):return json.loads(p.read_text())
def wr(p,d):p.write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
files={}
def add(p,n):
 assert p.is_file() and not p.is_symlink(),p
 files[n]=p
for p in (W/'runs/public-a').rglob('*'):
 if p.is_file() and not p.is_symlink() and 'artifacts' not in p.parts and 'import-overlay' not in p.parts and p.name!='external-inputs.json':add(p,'runs/public-a/'+str(p.relative_to(W/'runs/public-a')))
for folder in ['sources','successful-targets','input-manifests']:
 for p in (W/folder).rglob('*'):
  if p.is_file():add(p,folder+'/'+str(p.relative_to(W/folder)))
for n in ['runner.py','stage.py','external-inputs-carrier.json','import-source-audit.json']:add(W/n,n)
final=rd(W/'successful-targets/ExtractedWithdrawalCallerPublic.json');assert final['exit_status']==0 and final['axioms']['passed'] and len(final['axioms']['reports'])==2
assert final['key']['source_sha256']==sha(W/'sources/ExtractedWithdrawalCallerPublic.lean')
assert final['process_swaps']==0 and final['cgroup_swap_current']=='0'
for v in final['objects'].values():assert sha(Path(v['path']))==v['sha256']
summary={'scope':'Actual ASWP encoder success plus actual semantic serializer success on fixed all-field carrier implies live parsePublic; supplied public requires explicit equality to fixed wire.',
'final_source_sha256':final['key']['source_sha256'],'final_objects':final['objects'],'final_axioms':final['axioms'],
'receipt':{k:final[k] for k in ['target','exit_status','wall_seconds','sampled_cgroup_peak_bytes','peak_process_rss_kib','process_swaps','cgroup_swap_current']},
'checked_predecessors':len(rd(W/'import-source-audit.json')),'predecessor_replay':False,
'limits':{'MemoryHigh':6*2**30,'MemoryMax':8*2**30,'MemorySwapMax':0},
'remaining':['actual terminal/verifier reachability','semantic serializer success premise','supplied public equality and omitted metadata/account binding','extraction-tool correctness']}
wr(O/'check-summary.json',summary);add(O/'check-summary.json','check-summary.json');add(Path(__file__),'collect.py')
wr(O/'archive-members.json',{n:{'sha256':sha(p),'bytes':p.stat().st_size} for n,p in sorted(files.items())})
with tarfile.open(O/'public-check-evidence.tar.gz','w:gz') as t:
 for n,p in sorted(files.items()):t.add(p,arcname=n,recursive=False)
wr(O/'archive-pin.json',{'sha256':sha(O/'public-check-evidence.tar.gz'),'bytes':(O/'public-check-evidence.tar.gz').stat().st_size,'members':len(files)})
print((O/'archive-pin.json').read_text())
