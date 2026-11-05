"""Additive packet checks; retain predecessor gates and reject premature credit."""
from pathlib import Path
import json,hashlib,copy,re
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
closed=load('NGQ_CLOSED.json');delta=load('NGQ_LEDGER_DELTA.json');native=load('NGQ_NATIVE_RESULTS.json')
def root_credit(c,d):
 assert c['new_composed_rows']==0 and c['new_composed_functions']==0 and c['functions']==[]
 assert c['target']['row']=='TX1:168' and c['target']['status']=='OPEN'
 assert d['rows']==[] and d['composed_rows_added']==0 and d['closed_by_this_job']==0
 assert d['before']['TX1:168']=='OPEN' and d['after']['TX1:168']=='OPEN'
 assert d['assumptions_removed']==d['assumptions_added']==d['assumptions_discharged']==[]
root_credit(closed,delta)
mutations=0
for kind in ['target','delta','trust']:
 c=copy.deepcopy(closed);d=copy.deepcopy(delta)
 if kind=='target':c['target']['status']='CLOSED'
 if kind=='delta':d['rows']=[{'row':'TX1:168','status':'CLOSED'}]
 if kind=='trust':d['assumptions_removed']=['P6']
 try:root_credit(c,d)
 except AssertionError:mutations+=1
 else:raise AssertionError('Credit validator accepted planted '+kind)
assert mutations==3
assert len(native['runs'])==60
by={r['attempt']:r for r in native['runs']}
for pair in native['selected']:
 assert pair['matched_fragment'] and not pair['composed_row_credit']
 a,b=[load(k+'/receipt.json') for k in [pair['positive'],pair['negative']]]
 assert a['native_command']==b['native_command'] and a['root_package']==b['root_package']
 assert a['env']['RUSTFLAGS']==b['env']['RUSTFLAGS'].replace(' --cfg NGQ_invert','')
 assert by[pair['positive']]['status']=='PASS' and by[pair['negative']]['status']=='ASSERTION_FAILED'
 for r in [a,b]:
  raw=(E/r['attempt']/'stdout.log').read_text()
  assert not any(t in raw for t in ['CBMC timed out','CBMC failed','unwinding assertion'])
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  graph=load(r['attempt']+'-graph-check.json');lock=load(r['attempt']+'-lock-check.json')
  assert graph['graph_matches_frozen'] and not graph['edge_errors'] and lock['unchanged']
  assert '--locked' not in r['native_command']
for p in list(E.glob('NGQ_K[0-9][0-9][0-9]/receipt.json'))+list(E.glob('NGQ_L[0-9][0-9][0-9]/receipt.json'))+[E/'NGQ_E001/receipt.json']:
 r=json.loads(p.read_text());limits=r['limits']
 assert limits=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 assert str(r['swaps'])=='0',p
admissible={'propext','Classical.choice','Quot.sound'}
expected=sum(load('NGQ_AUDIT_ROOTS.json')['groups'],[]);found=[]
for p in sorted((E/'NGQ_audit').glob('batch*/proof*.json'))+sorted((E/'NGQ_audit/finalnew').glob('proof*.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0
 for row in r['results']:
  assert row['equal'] and set(row['walked_axioms'])<=admissible
  assert sorted(row['walked_axioms'])==sorted(row['collect_axioms'])
  found.append(row['root'])
assert found==expected and len(found)==len(set(found))
f=load('NGQ_audit/fixtures/fixtures.json');assert f['exit_status']==0 and len(f['results'])==8
for i,row in enumerate(f['results']):
 assert row['equal']
 assert (len(row['walked_axioms'])==1 and row['walked_axioms'][0].startswith('NEP_Planted.')) if i<4 else not row['walked_axioms']
scan=[json.loads(l) for l in (E/'NGQ_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
# Same source-derived import headers; never learn expected headers from candidate scan.
for d in map(json.loads,(E/'NGQ_EXPECTED_IMPORTS.jsonl').read_text().splitlines()):
 p=E/(d['module']+'.lean')
 if p.exists():
  assert d['source_sha256']==hashlib.sha256(p.read_bytes()).hexdigest(),p
  ns=['Init']
  for n in re.findall(r'(?m)^import\s+([\w.]+)',p.read_text()):
   if n not in ns:ns.append(n)
  assert d['imports']==ns,p
assert load('NGQ_WALKER_PIN.json')['byte_identical']
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
print(json.dumps({'status':'PASS','native_attempts':60,'matched_fragments':len(native['selected']),'raw_roots':len(found),'fixtures':8,'scanned_modules':len(scan),'premature_credit_mutations_rejected':mutations,'rows_closed':0},indent=2))
