from pathlib import Path
import json,re,hashlib,subprocess
D=Path(__file__).parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lean=[json.loads(p.read_text()) for p in sorted(D.glob('lean*-receipt.json'))];native=[json.loads(p.read_text()) for p in sorted(D.glob('native*-receipt.json'))]
assert len(lean)==100 and [r['attempt'] for r in lean]==list(range(65200,65300))
accepted={}
for r in lean:
 assert r['admission_allowed'] is True and r['admission_exit']==0
 assert r['resource_caps']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 assert sha(D/('lean'+str(r['attempt'])+'-source.lean.txt'))==r['source_sha256']
 if r['exit']==0:
  accepted[r['module']]=r
  assert 'sorryAx' not in r['print_axioms']
  for ax in re.findall(r'depends on axioms: \[([^\]]*)\]',r['print_axioms']):assert set(ax.split(', ')) <= {'propext','Classical.choice','Quot.sound'}
for r in native:assert r['admission_allowed'] is True and r['admission_exit']==0 and r['exit']==0
assert all(r['swaps']=='0' for r in lean+native)
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();rows=[]
for p in sorted(D.glob('PV_DIAG6_*.lean')):
 r=accepted[p.stem];assert sha(p)==r['source_sha256'],p
 path=str(p.relative_to(Path.cwd()));b=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip()
 assert subprocess.check_output(['git','show',rev+':'+path])==p.read_bytes()
 rows.append(dict(module=p.stem,path=path,source_sha256=sha(p),blob=b,source_revision=rev,accepted_attempt=r['attempt']))
(D/'final-source-identity.json').write_text(json.dumps(dict(source_revision=rev,rows=rows),indent=2)+'\n')
summary=dict(lean_attempts=len(lean),lean_pass=sum(r['exit']==0 for r in lean),lean_fail=[r['attempt'] for r in lean if r['exit']!=0],native_scopes=len(native),kani=0,peak_rss_kib=max(int(r['peak_rss_kib']) for r in lean+native),sum_wall_seconds=sum(r['wall_seconds'] for r in lean+native),swaps=0,new_theorems=85,source_revision=rev,audits=[r for r in lean if r['attempt']>=65297])
(D/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');(D/'attempts.json').write_text(json.dumps(dict(lean=lean,native=native),indent=2)+'\n')
print({k:v for k,v in summary.items() if k!='audits'})
