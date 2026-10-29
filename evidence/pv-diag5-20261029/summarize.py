from pathlib import Path
import json,re,hashlib
D=Path(__file__).parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[json.loads(p.read_text()) for p in sorted(D.glob('lean*-receipt.json'))];native=[json.loads(p.read_text()) for p in sorted(D.glob('native*-receipt.json'))]
assert [r['attempt'] for r in records]==list(range(65000,65100))
latest={r['module']:r for r in records if r['exit']==0};sources=[]
for p in sorted(D.glob('PV_DIAG5_*.lean')):
 r=latest[p.stem];assert sha(p)==r['source_sha256'],p
 assert p.read_bytes()==(D/('lean'+str(r['attempt'])+'-source.lean.txt')).read_bytes()
 sources.append(dict(module=p.stem,path=str(p),sha256=sha(p),attempt=r['attempt'],theorems=re.findall(r'^theorem (\S+)',p.read_text(),re.M)))
for r in records+native:
 assert r['admission_exit']==0 and r['admission_allowed'] is True
 assert r['resource_caps']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 assert r['swaps']=='0'
 if r['exit']==0 and r['kind']=='lean':
  assert 'sorryAx' not in r['print_axioms']
  for ax in re.findall(r'depends on axioms: \[([^]]+)\]',r['print_axioms']):assert set(re.split(r',\s*',ax.strip()))<={'propext','Classical.choice','Quot.sound'}
assert json.loads((D/'final-post.json').read_text())['mismatches']==[]
def seconds(s):
 v=[float(x) for x in s.split(':')];return sum(x*60**i for i,x in enumerate(v[::-1]))
out=dict(lean_attempts=len(records),lean_success=sum(r['exit']==0 for r in records),failed=[dict(attempt=r['attempt'],module=r['module'],exit=r['exit']) for r in records if r['exit']],native_scopes=len(native),kani=0,all_swaps_zero=True,total_gnu_wall_seconds=round(sum(seconds(r['gnu_wall']) for r in records+native),2),peak_rss_kib=max(int(r['peak_rss_kib']) for r in records+native),sources=sources,new_theorems=sum(len(r['theorems']) for r in sources),final_closure_objects=json.loads((D/'final-post.json').read_text())['checked'])
(D/'summary.json').write_text(json.dumps(out,indent=2)+'\n');(D/'attempts.json').write_text(json.dumps(records+native,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='sources'},indent=2))
