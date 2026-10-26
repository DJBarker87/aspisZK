"""Read-only receipt, final source, allowed-axiom and change-scope audit."""
from pathlib import Path
import hashlib,json,re,subprocess,datetime
R=Path(__file__).resolve().parents[2];B=Path(__file__).resolve().parent
receipts=[json.loads((B/f'JFw_{i:03}'/'receipt.json').read_text()) for i in range(1,101)]
allowed={'propext','Classical.choice','Quot.sound'};good=[]
for i,r in enumerate(receipts,1):
 assert r['attempt']==f'JFw_{i:03}'
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and len(r['sources'])==1
 assert r['swaps']=='0'
 for s,h in r['source_hashes'].items():assert hashlib.sha256((B/r['attempt']/'sources'/s).read_bytes()).hexdigest()==h
 if r['exit_status']==0:
  assert r['print_axioms'],r['attempt']
  for line in r['print_axioms']:
   m=re.search(r'\[([^]]*)\]',line)
   if m:assert set(m[1].split(', '))<=allowed,(r['attempt'],line)
  good.append(r)
modules=[]
for p in sorted((R/'lean').glob('JFw_*.lean')):
 sha=hashlib.sha256(p.read_bytes()).hexdigest()
 matches=[r['attempt'] for r in good if r['source_hashes'].get(p.name)==sha]
 assert matches,('No accepted final hash',p.name)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),p.name
 modules.append(dict(module=p.stem,sha256=sha,accepted_attempts=matches))
changed=subprocess.check_output(['git','diff','--name-only','7bb02992c69691fdb8088381d2f5c8e3027098e9'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/JFw_') or p.startswith('evidence/joint-fixture4-20261026/') for p in changed)
ledger=json.loads((B/'JFw_LEDGER_DELTA.json').read_text());assert all(t['unchanged'] for t in ledger['targets'])
result=dict(lean_attempts=100,kani_runs=0,passed=len(good),failed=100-len(good),final_modules=modules,
 peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,
 total_wall_seconds=sum(r['wall_seconds'] for r in receipts),exit_statuses={str(c):sum(r['exit_status']==c for r in receipts) for c in sorted({r['exit_status'] for r in receipts})},
 final_attempt_error='Missing PFin_Attach while importing cached Rc6_Top; no combined Inputs proof/current-top audit obtained',
 scope='One scope at a time, four early one-file scopes then one persistent sequential scope. No package replay.',
 formal_release='Not claimed; inherited SInt2/cache proof evidence, no fresh frozen artifact rebuild',
 delta=ledger['delta'])
a=json.loads((B/'JFw_admission005.json').read_text());z=json.loads((B/'JFw_admission005retry1.json').read_text())
result['reservation_wait_deviation']=dict(denial='JFw_admission005.json',retry='JFw_admission005retry1.json',elapsed_seconds=(datetime.datetime.fromisoformat(z['utc'])-datetime.datetime.fromisoformat(a['utc'])).total_seconds(),required_seconds=180,allowed_on_retry=z['allowed'],explanation='Early aggregate-reservation retry; admission was still required and passed, caps unchanged. No claim of full timing-policy compliance.')
(B/'JFw_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='final_modules'},indent=2))
