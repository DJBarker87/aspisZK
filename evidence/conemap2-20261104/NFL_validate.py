#!/usr/bin/env python3
"""Read-only consistency/source-pin validation. Does not execute proof tools."""
import collections,hashlib,json,lzma,pathlib,subprocess,time
start=time.monotonic();D=pathlib.Path(__file__).resolve().parent;R=D.parent.parent
m=json.loads((D/'NFL_ROW_TO_CONE.json').read_text());l=json.loads(lzma.open(R/'evidence/ledger6-20261104/NFK_LEDGER.json.xz').read())
li={r['row']:r for r in l['rows']};mi={r['row']:r for r in m['rows']}
assert len(li)==len(mi)==587 and set(li)==set(mi)
for p,h in m['input_sha256'].items():assert hashlib.sha256((R/p).read_bytes()).hexdigest()==h,p
raw=lzma.open(R/'evidence/ledger6-20261104/NFK_LEDGER.json.xz').read()
assert hashlib.sha256(raw).hexdigest()==m['uncompressed_ledger_sha256']
assert m['uncompressed_ledger_sha256'] in (R/'evidence/ledger6-20261104/NFK_LEDGER.json.sha256').read_text()
slices=json.loads((R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json').read_text())['slices']
source={}
for r in li.values():
 f=r['source_file']
 if f not in source:source[f]=subprocess.check_output(['git','show',l['frozen_revision']+':'+f],cwd=R)
 assert hashlib.sha256(source[f]).hexdigest()==r['source_file_sha256'],f
 a,b=r['frozen_body_byte_range'];assert hashlib.sha256(source[f][a:b]).hexdigest()==r['frozen_body_sha256'],r['row']
 x=mi[r['row']];assert x['function']==r['function'] and x['composed_status']==r['composed_status'] and x['frozen_body_sha256']==r['frozen_body_sha256']
 assert x['slices']==[s for s in slices if r['function'] in slices[s]['functions']]
 idx={z['function']:z for z in li.values() if z['transaction']==r['transaction']}
 assert len({a['cone'] for a in x['assignments']})==len(x['assignments'])
 for ass in x['assignments']:
  path=ass['frozen_call_path'];assert path[-1]==r['function']
  if ass['cone']=='S10':assert ass['role']=='all-site inventory'
  else:
   assert path[0] in m['anchors'][ass['cone']]['functions']
   for a,b in zip(path,path[1:]):assert b in idx[a]['canonical_callees'] and b in idx
assert collections.Counter(x['composed_status'] for x in mi.values())=={'CLOSED':219,'QUALIFIED':2,'OPEN':366}
for c,n in m['cone_counts'].items():
 rr=[x for x in mi.values() if any(a['cone']==c for a in x['assignments'])]
 assert len(rr)==n['total']
 for status in ['CLOSED','QUALIFIED','OPEN']:assert sum(x['composed_status']==status for x in rr)==n[status]
 # Independently compute full directed closure, not just path validity.
 for tx in ['TX1','TX2']:
  idx={r['function']:r for r in li.values() if r['transaction']==tx}
  reached=set(idx) if c=='S10' else set(m['anchors'][c]['functions']) & set(idx)
  while True:
   new=reached|{g for f in reached for g in idx[f]['canonical_callees'] if g in idx}
   if new==reached:break
   reached=new
  assert reached=={x['function'] for x in rr if x['transaction']==tx}
for s in slices:
 rr=[x for x in mi.values() if s in x['slices']]
 expected=l['NFK_slices'][s];assert len(rr)==expected['total']
 for status in ['CLOSED','QUALIFIED','OPEN']:assert sum(x['composed_status']==status for x in rr)==expected[status]
prem=json.loads((D/'NFL_PREMISE_COVERAGE.json').read_text());rc=json.loads((R/'evidence/recount7-20261026/Rc7_premises.json').read_text())
assert {p['id'] for p in prem}=={p['id'] for p in rc['rows'] if p['classification']=='P'}
assert len(prem)==32 and all(not p['new_discharge'] for p in prem)
for p in prem:assert set(p['candidate_rows'])<=set(mi)
assert not m['no_cone_rows']
assert all(f.stat().st_size<=20*1024*1024 for f in D.iterdir() if f.is_file())
path='evidence/recount10-20261026/Rc10_059/receipt.json'
rawreceipt=subprocess.check_output(['git','show',m['source_revision']+':'+path],cwd=R);h=json.loads(rawreceipt)
review={'kind':'reused historical receipt review; no new compilation','source_revision':m['source_revision'],'path':path,'sha256':hashlib.sha256(rawreceipt).hexdigest(),'target':h['command'],'exit_status':h['exit_status'],'wall_seconds':h['wall_seconds'],'peak_rss_kib':h['peak_rss_kib'],'swaps':h['swaps'],'historical_source_revision':h['source_revision'],'historical_source_tree_dirty':h['source_tree_dirty'],'print_axioms':h['print_axioms'],'limitation':'Historical scoped retirements only; not replayed or transported to ledger frozen Rust revision.'}
(D/'NFL_HISTORICAL_RECEIPT_REVIEW.json').write_text(json.dumps(review,indent=2)+'\n')
result={'kind':'receipt-only mapping validation','exit_status':0,'wall_seconds':round(time.monotonic()-start,6),'source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'rows':len(mi),'frozen_source_files_checked':len(source),'frozen_body_hashes_checked':len(li),'raw_Rc7_P_rows_checked':len(prem),'cone_counts':m['cone_counts'],'checks':['Input hashes and uncompressed ledger sidecar','Every frozen source and function body hash against frozen Git revision','Every assignment path valid in same transaction canonical graph','Independent complete graph closure agrees with all assigned memberships','Occurrence and slice counts agree with NFK','All 32 Rc7 P rows crosswalked; no new discharge','Every output below 20 MiB'],'lean_compiles':0,'kani_runs':0,'axioms':'N/A: no new theorem; historical receipt audited read-only','peak_rss':'not sampled; small Python audit, not formal release','swap':'not sampled; no build launched'}
(D/'NFL_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='cone_counts'}))
