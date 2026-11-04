from pathlib import Path
import json,hashlib,re,subprocess
E=Path('evidence/pv-stx-20261104');latest={};receipts=[]
for p in sorted(E.glob('receipt-*.json')):
 r=json.loads(p.read_text());receipts.append(r)
 assert r['exit'] is not None and r['wall'] is not None and r['peak_rss_kib'] is not None and r['swaps']=='0',p
 prep_input=E/'preparations'/(str(r['attempt'])+'.json')
 assert hashlib.sha256(prep_input.read_bytes()).hexdigest()==r['deps_fingerprint'],p
 if r['accepted']:
  assert not any('sorryAx' in x for x in r['print_axioms_summary_based']),p
  for line in r['print_axioms_summary_based']:
   names=re.search(r'depends on axioms: \[(.*?)\]',line,re.S)
   if names: assert set(names[1].replace(' ','').replace('\n','').split(',')) <= {'propext','Classical.choice','Quot.sound'},p
  latest[r['target']]=r
current=[]
for m,r in latest.items():
 raw=Path('lean/'+m+'.lean').read_bytes()
 assert hashlib.sha256(raw).hexdigest()==r['source_sha256'],m
 prep=E/('prepare-'+m+'.json')
 assert hashlib.sha256(prep.read_bytes()).hexdigest()==r['deps_fingerprint'],m
 current.append(dict(module=m,attempt=r['attempt'],source_sha256=r['source_sha256'],object_sha256=r['object_sha256'],print_axioms_summary_based=r['print_axioms_summary_based']))
binary=json.loads((E/'binary-observation.json').read_text())
assert binary['sha256']=='fda587d25a66604a973bbc2947a4416ba373b56dd8c98655991c1b6eaa240b68'
helptext=(E/'N91800/output.log').read_text();assert '-use-fuel' in helptext and not re.search(r'^\s+-\S*state\S*\b',helptext,re.M)
assert all(p.stat().st_size<=20*2**20 for p in E.rglob('*') if p.is_file())
changed=subprocess.check_output(['git','diff','--name-only','fd4a644fd4'],text=True).splitlines()
assert not [p for p in changed if p.startswith(('crates/','programs/','tools/r1-cost-probe/'))]
audit=json.loads((E/'raw-audit/results.json').read_text())
assert audit['complete'] and audit['unresolved_constants']==0 and len(audit['roots'])==42
result=dict(current_modules=current,lean_executions=len(receipts),failed_executions=[r['attempt'] for r in receipts if not r['accepted']],focused_executions=sum(r['attempt']<=91796 for r in receipts),audit_executions=sum(r['attempt']>=91797 for r in receipts),native_executions=1,kani_executions=0,max_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),summary_axioms_only=False,summary_axioms_only_for_new_modules=True,raw_audit=dict(attempt=91799,complete=True,roots=42,unresolved=0,standard_axioms_only=True,scope='historical substrate at f9e335854e; new continuation modules NOT raw-audited',covers_current_new_modules=False),forbidden_paths_changed=False,rows_removed=[],target='not yet established',remaining='source_entry_world/full source call closure/native interpretation/five deployed projections')
(E/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
print('validated',len(current),'current modules;',len(receipts),'Lean executions; historical 42 raw roots complete; new continuation closure unaudited')
