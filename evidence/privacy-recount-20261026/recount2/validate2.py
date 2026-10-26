"""Mechanical consistency/git-binding checks; not a theorem or native gate."""
from pathlib import Path
from collections import Counter
import subprocess,json,re,hashlib
P=Path(__file__).resolve().parent;ROOT=P.parents[2];OUT=P.parent
base='1096508d6e2880bfdea8ddb037934d22838fffa0'
old=json.loads((OUT/'rows.json').read_text());rows=json.loads((P/'rows2.json').read_text());tot=json.loads((P/'totals2.json').read_text());rec=json.loads((P/'receipts.json').read_text());manifest=json.loads((P/'manifest.json').read_text())
assert len(rows)==403 and len(set(r['id'] for r in rows))==403
assert [r['id'] for r in rows[:400]]==[r['id'] for r in old]
for before,after in zip(old,rows):
 for k in ['id','name','meaning','classification','definition']:
  assert before.get(k)==after.get(k),(before['id'],k)
 assert after['recount1_status']==before['recount_status']
for r in rows:
 assert r['recount2_status'] in ['OPEN','REDUCED','EVIDENCED','CLOSED-ON-RESEARCH','CLOSED-ON-CANDIDATE']
 assert bool(r.get('dependency_bucket'))==(r['recount2_status']=='OPEN'),r['id']
 assert r['recount2_basis'] and r['recount2_evidence']
 if r['recount2_status']=='REDUCED':assert r['residual_fields'],r['id']
 if r['recount2_status'].startswith('CLOSED'):assert r.get('theorem'),r['id']
for k,rs in [('recount2_same400',rows[:400]),('recount2_all',rows)]:
 assert tot[k]['rows']==len(rs)
 assert tot[k]['classes']==dict(Counter(r['classification'] for r in rs))
 assert tot[k]['statuses']==dict(Counter(r['recount2_status'] for r in rs))
 assert tot[k]['open_dependencies']==dict(Counter(r['dependency_bucket'] for r in rs if r['recount2_status']=='OPEN'))
assert len(rec)==15 and [r['attempt'] for r in rec]==list(range(24300,24315))
assert Counter(r['exit_status'] for r in rec)=={'0':13,'1':2}
allowed={'propext','Classical.choice','Quot.sound'}
for r in rec:
 assert r['compiler_invoked'] and r['swap']=='0'
 assert r['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=128,Lean_M=7000)
 helper=P/'helpers'/(r['module']+'.lean');assert hashlib.sha256(helper.read_bytes()).hexdigest()==r['source_sha256']
 for line in helper.read_text().splitlines():assert line.startswith(('import R1Z.','set_option pp.explicit true','#check @','#print ')),line
 if r['exit_status']=='0':
  assert r['print_axioms'] and not r['errors']
  for a in r['print_axioms']:
   if 'depends on axioms:' in a:assert set(re.search(r'\[([\s\S]*)\]',a)[1].replace('\n','').split(', '))<=allowed,a
 fresh='\n'.join(r['print_axioms'])
for r in rows[:400]:
 if r['recount2_status']=='CLOSED-ON-CANDIDATE' and r['recount1_status']!='CLOSED-ON-CANDIDATE':
  assert any(r['theorem'] in '\n'.join(x['print_axioms']) and x['exit_status']=='0' for x in rec),r['id']
assert sum(r['recount2_status']=='CLOSED-ON-CANDIDATE' and r['recount1_status']!='CLOSED-ON-CANDIDATE' for r in rows[:400])==27
# Every stored git snapshot must reproduce exactly from the frozen object.
for x in manifest:
 data=Path(x['local']).read_bytes();assert hashlib.sha256(data).hexdigest()==x['sha256'],x['local']
 original=subprocess.check_output(['git','show',x['revision']+':'+x['path']]);assert original==data,x['local']
resolved=json.loads((P/'resolved-definitions.json').read_text());assert len(resolved)==399 and all(r['resolved'] for r in resolved)
oldledger=subprocess.check_output(['git','show',base+':design/PRIVACY-LEDGER-20261026.md'])
ledger=Path('design/PRIVACY-LEDGER-20261026.md').read_bytes();assert ledger.startswith(oldledger)
for path in ['ROWS.md','rows.json','totals.json','pins.json','METHOD.md']:
 oldfile=subprocess.check_output(['git','show',base+':evidence/privacy-recount-20261026/'+path]);assert (OUT/path).read_bytes()==oldfile,path
changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
assert all(p=='design/PRIVACY-LEDGER-20261026.md' or p.startswith('evidence/privacy-recount-20261026/') for p in changed)
assert not any(p.endswith(('.olean','.so','.tar','.elf')) for p in changed)
assert subprocess.run(['git','diff','--check'],capture_output=True).returncode==0
result=dict(passed=True,rows_reviewed=403,inherited_preserved=400,original_defining_paths_resolved=len(resolved),git_snapshots_verified=len(manifest),lean_invocations=15,lean_exit0=13,lean_diagnostic_exit1=2,kani_invocations=0,new_candidate_source_closures=27,new_proofs=0,endpoint_premises_removed=0,source_implementation_changes=0,source_revision=base,scope='mechanical audit consistency only; no full dependency replay')
(P/'validation2.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
