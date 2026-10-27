"""Static evidence audit only; does not launch or repair build infrastructure."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent;R=P.parents[1]
receipts=[json.loads(f.read_text()) for f in sorted(P.glob('JFv_TX2_*/receipt.json'))]
allowed={'propext','Classical.choice','Quot.sound'}
accepted=[]
for r in receipts:
 if int(r['attempt'].rsplit('_',1)[1])>=45:
  paths=r['env']['LEAN_PATH'].split(':')
  assert paths[0]=='/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects'
for f in sorted((R/'lean').glob('JFv_TX2_*.lean')):
 sha=hashlib.sha256(f.read_bytes()).hexdigest()
 candidates=[r for r in receipts if r['exit_status']==0 and r['source_hashes'].get(f.name)==sha]
 assert candidates,f'No passing current source: {f}'
 r=candidates[-1];s=f.read_text();ns=re.search(r'namespace ([\w.]+)',s)[1]
 names=re.findall(r'^theorem\s+(\w+)',s,re.M)
 for name in names:
  matches=[line for line in r['print_axioms'] if "'"+ns+'.'+name+"'" in line]
  assert len(matches)==1,(name,matches)
  line=matches[0];ax=set(re.search(r'\[(.*?)\]',line)[1].split(', ')) if '[' in line else set()
  assert ax<=allowed,(name,ax)
  assert '#print axioms '+name in s,(f,name)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats|maxRecDepth',s),f
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 accepted.append(dict(module=f.stem,sha256=sha,attempt=r['attempt'],theorems=names,axioms=r['print_axioms']))
charged=max(int(f.stem.rsplit("_",1)[1]) for f in P.glob("JFv_TX2_[0-9][0-9][0-9].json"))
summary=dict(charged_attempts=charged,lean_processes=len(receipts),passes=sum(r['exit_status']==0 for r in receipts),rejects=sum(r['exit_status']!=0 for r in receipts),preflight_without_lean=1,kani_runs=0,delivered_modules=len(accepted),wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=sum(int(r['swaps']) for r in receipts),stop='Budget exhausted' if charged==100 else 'In progress after lead path ruling',remaining_lean_attempts=100-charged,remaining_kani_runs=10)
(P/'JFv_TX2_VALIDATION.json').write_text(json.dumps(dict(summary=summary,accepted=accepted),indent=2)+'\n')
(P/'JFv_TX2_RECORDS_MANIFEST.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(summary,indent=2))
