from pathlib import Path
import json,re,hashlib,subprocess,collections
P=Path(__file__).resolve().parent;B=P.parent
rows=json.loads((P/'rows4.json').read_text());old=json.loads((B/'recount3/rows3.json').read_text());t=json.loads((P/'totals4.json').read_text());pins=json.loads((P/'pins.json').read_text())
assert [r['id'] for r in rows]==[r['id'] for r in old] and len(rows)==len({r['id'] for r in rows})==407
for r,o in zip(rows,old):
 for f in ['id','name','classification','recount3_status']:assert r[f]==o[f],(r['id'],f)
 assert r['recount4_basis'] and r['recount4_evidence']
 assert (r['dependency_bucket'] in ['a','b','c','d'])==(r['recount4_status']=='OPEN')
 assert r['in_headline_closure4'] in ['research','candidate','neither']
 assert r['definition_witnesses'] or r['id'] in ['V271','V380-inversion','V400','V401','V402','V403','V404','V405','V406']
counts=lambda f:dict(collections.Counter(r[f] for r in rows))
assert counts('recount4_status')==t['statuses'];assert counts('recount4_class')==t['classes']
assert t['statuses']==dict(REDUCED=176,OPEN=95,**{'CLOSED-ON-RESEARCH':87,'EVIDENCED':14,'CLOSED-ON-CANDIDATE':35})
assert t['open_dependencies']==dict(a=23,b=55,c=1,d=16)
assert t['closure_routes']==dict(extraction=27,**{'extraction bridge':1,'P6 gate':6,'axiom diagnostic':1})
assert sum(t['statuses'].values())==407 and sum(t['classes'].values())==407
assert t['candidate_closure_imports']==dict(candidate=29,neither=6)
assert t['all_row_imports']==dict(research=160,candidate=137,neither=110)
by={r['id']:r for r in rows}
assert by['V246']['closure_route']=='extraction'
assert by['V164']['overlap_recount4']=='V240' and by['V406']['overlap_recount4']=='V329'
assert by['V270']['in_headline_closure4']=='neither'
assert all(by[i]['closure_route']=='P6 gate' for i in ['V177','V179','V180','V185','V186','V195'])
assert by['V380-inversion']['dependency_bucket']=='b' and by['V380']['recount4_status']=='REDUCED'
assert all(by[i]['recount4_status']=='REDUCED' for i in ['V152','V153','V154'])
base=subprocess.check_output(['git','show',pins['worktree_base']+':design/PRIVACY-LEDGER-20261026.md'])
ledger=Path('design/PRIVACY-LEDGER-20261026.md').read_bytes();assert ledger.startswith(base)
assert ledger.count(b'## Recount 4 2026-10-27 (B)')==1
assert len(re.findall(r'^\|V', (B/'ROWS4.md').read_text(),re.M))==407
receipts=json.loads((P/'receipts.json').read_text());assert len(receipts)==20 and [x['attempt'] for x in receipts]==list(range(44500,44520))
assert sum(x['exit']=='0' for x in receipts)==16
allowed={'propext','Classical.choice','Quot.sound'}
for x in receipts:
 for field in ['module','source_revision','source_sha256','dependency_fingerprint','exit','wall','peak_RSS_KiB','swap','axioms']:assert field in x
 assert x['swap']=='0'
 for line in x['axioms']:
  m=re.search(r'\[([^]]*)\]',line)
  if m and x['exit']=='0':assert set(m[1].replace(' ','').split(','))<=allowed
 assert (P/x['log']).exists() and (P/x['time']).exists()
for x in json.loads((P/'checks.json').read_text()):
 raw=(P/x['source']).read_bytes();assert hashlib.sha256(raw).hexdigest()==x['sha256']
 assert x['module'].startswith('PV_Ledger_')
 assert not re.search(r'^(?:theorem|lemma|def|axiom|example|instance)\b',raw.decode(),re.M)
 assert not re.search(r'\b(sorry|admit|native_decide|bv_decide)\b',raw.decode())
manifest=json.loads((P/'manifest.json').read_text())
for x in manifest:assert hashlib.sha256((P/x['snapshot']).read_bytes()).hexdigest()==x['sha256'],x['path']
reuse=[]
for n in ['43381','43382']:
 x=json.loads((P/'reused/op223'/f'{n}.json').read_text());raw=subprocess.check_output(['git','show',pins['revisions']['op223']+':docs/research/v8-r0-zk-20261009/lean/'+x['module']+'.lean'])
 assert x['exit_status']==0 and hashlib.sha256(raw).hexdigest()==x['source_sha256'];reuse.append(n)
wire=json.loads((P/'wire-audit4.json').read_text());assert len(wire)==27 and all(x['edges_valid'] for x in wire)
assert sum(by[x['id']]['in_headline_closure4']=='candidate' for x in wire)==26
result=dict(rows=407,original_ledger_prefix_unchanged=True,statuses=t['statuses'],classes=t['classes'],open_buckets=t['open_dependencies'],candidate_routes=t['closure_routes'],headline_candidate_closures=t['candidate_closure_imports'],statement_attempts=20,statement_passes=16,statement_failures=4,standard_axioms_on_success=True,source_records_hashed=len(manifest),wire_rows_checked=27,accepted_original_op223_receipts_exact_source_match=reuse,kani_runs=0,new_proofs=0,premises_removed_added_weakened=[0,0,0],target='not yet established')
(P/'validation4.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
