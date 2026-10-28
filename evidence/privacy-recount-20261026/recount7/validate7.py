from pathlib import Path
import json,hashlib,collections,re,subprocess
P=Path(__file__).resolve().parent;B=P.parent
load=lambda p:json.loads(p.read_text())
r=load(P/'rows7.json');old=load(B/'recount6/rows6.json');t=load(P/'totals7.json');pins=load(P/'pins.json');m=load(P/'manifest.json')
assert len(r)==len(old)==407 and len({x['id'] for x in r})==407
expected={'V217','V220','V230','V239','V256','V257','V258','V259','V260'}
assert {a['id'] for a,b in zip(r,old) if a['recount7_status']!=b['recount6_status']}==expected
assert collections.Counter(x['recount7_status'] for x in r)==t['statuses']
assert collections.Counter(x['recount7_class'] for x in r)==t['classes']=={'P':400,'T':3,'C':4}
assert collections.Counter(x['dependency_bucket'] for x in r if x['recount7_status']=='OPEN')==t['open_dependencies']=={'a':2,'b':56,'c':5,'d':14}
for a,b in zip(r,old):
 assert a['id']==b['id']
 for k,v in b.items():
  if k.startswith('recount') or k.startswith('definition_witnesses') or k.startswith('import_witnesses') or k.startswith('in_headline_closure') or k in ['baseline_status','classification','definition','name','meaning']:
   assert a[k]==v,(a['id'],k)
 assert (a['dependency_bucket'] in 'abcd') if a['recount7_status']=='OPEN' else a['dependency_bucket'] is None
for x in m:
 raw=(P/x['snapshot']).read_bytes();assert hashlib.sha256(raw).hexdigest()==x['sha256'],x['path']
 assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['blob'],x['path']
 assert x['revision']==pins['revisions'][x['ref']],x['path']
assert all(re.fullmatch('[a-f0-9]{40}',p) for p in pins['revisions'].values())
audit=load(P/'definition-audit7.json');assert {a['id'] for a in audit}=={a['id'] for a in r}
nonformal={'V380-inversion','V400','V401','V402','V403','V404','V405','V406'}
assert {a['id'] for a in audit if not a['sources']}==nonformal
for a in audit:
 if a['id'] not in nonformal:assert all('declaration' in s for s in a['sources'])
by={x['id']:x for x in r}
for id in ['V178','V179','V182','V195','V233']:
 assert by[id]['closure_route']=='structural (K-1 substitute)' and by[id]['recount7_status']=='CLOSED-ON-CANDIDATE'
 assert by[id]['kani_status7'].startswith('SUSPENDED')
assert by['V184']['closure_route']=='structural stdlib' and by['V184']['kani_status7'].startswith('SUSPENDED')
for id in ['V152','V153','V154']:
 assert by[id]['raw_family_classification7'].startswith('identification_unsatisfiable')
 assert by[id]['honest_family_classification7']=='discharged at honest family' and by[id]['recount7_status']=='REDUCED'
assert t['premises_removed_added_weakened']==[0,0,0] and t['observer_logs_errors']=='coverage gap'
assert len(load(P/'closure-audit7.json'))==15
assert len(load(P/'receipt-audit7.json'))==12
for a in load(P/'receipt-audit7.json'):assert a['exit']==0 and str(a['swap'])=='0' and a['axioms_standard'] and a['axiom_reports']>0
checks=load(P/'native-pin-checks7.json');ex=load(P/'native-pin-exceptions7.json')
assert len(checks)==60 and sum(not c['matches'] for c in checks)==2
assert len(ex)==2 and all(c['selected_body_match'] for c in ex)
cs=load(P/'import-closures7.json')
assert all(not c['unresolved_project_modules'] for c in cs if c['ref'] in ['research','rw'])
for a in r:
 for w in a['import_witnesses7']:
  c=next(c for c in cs if c['ref']==w['ref'] and c['root']==w['root'])
  assert c['paths'][w['path'][-1]]==w['path']
for id in expected:assert by[id]['in_headline_closure7']=='neither'
assert collections.Counter(x['in_headline_closure7'] for x in r)==t['all_row_imports']
assert collections.Counter(x['in_headline_closure7'] for x in r if x['recount7_status']=='CLOSED-ON-CANDIDATE')==t['candidate_closure_imports']
rowsmd=(B/'ROWS7.md').read_text();assert len(re.findall(r'^\|V',rowsmd,re.M))==407
cor=(P/'CORRECTIONS7.md').read_text();assert all('| D'+str(n)+' |' in cor for n in range(301,357))
ledger=Path('design/PRIVACY-LEDGER-20261026.md').read_text();prefix=subprocess.check_output(['git','show',pins['worktree_base']+':design/PRIVACY-LEDGER-20261026.md'],text=True)
assert ledger.startswith(prefix) and ledger.count('## Recount 7 2026-10-28 (B)')==1
assert not list(P.glob('*.lean')) and not [f for f in P.rglob('*') if f.is_file() and f.stat().st_size>20*1024*1024]
v=dict(result='PASS',rows=407,status_changes=sorted(expected),historical_fields_preserved=True,manifest_entries=len(m),source_hashes=True,nonformal_rows_without_declaration=sorted(nonformal),closure_verdicts=15,reused_proof_receipts=12,native_file_pin_checks=60,native_file_matches=58,resolved_caller_deltas=2,actual_consumer_roots=len(cs),all_new_closures_absent_from_actual_roots=True,Lean_invocations=0,Kani_invocations=0,IDs_used=[],endpoint_premises_removed_added_weakened=[0,0,0],target='not yet established')
(P/'validation7.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
