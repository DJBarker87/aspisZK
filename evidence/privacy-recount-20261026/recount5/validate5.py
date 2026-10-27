from pathlib import Path
import json,hashlib,collections,subprocess,re
P=Path(__file__).resolve().parent;B=P.parent
rows=json.loads((P/'rows5.json').read_text());old=json.loads((B/'recount4/rows4.json').read_text());t=json.loads((P/'totals5.json').read_text());pins=json.loads((P/'pins.json').read_text())
assert len(rows)==len(old)==407 and [r['id'] for r in rows]==[r['id'] for r in old]
assert len({r['id'] for r in rows})==407
for r,o in zip(rows,old):
 for key in ['classification','meaning','name','definition','recount1_status','recount2_status','recount3_status','recount4_status','recount4_class']:
  assert r.get(key)==o.get(key),(r['id'],key)
 assert bool(r['dependency_bucket'])==(r['recount5_status']=='OPEN')
 assert r['recount5_evidence'] and r['recount5_basis']
assert dict(collections.Counter(r['recount5_status'] for r in rows))==t['statuses']
assert dict(collections.Counter(r['recount5_class'] for r in rows))==t['classes']
assert dict(collections.Counter(r['dependency_bucket'] for r in rows if r['recount5_status']=='OPEN'))==t['open_dependencies']
assert {r['id'] for r in rows if r['recount4_status']!=r['recount5_status']}=={'V181','V182'}
assert {r['id'] for r in rows if r['recount5_class']=='T'}=={'V329','V371','V406'}
assert t['premises_removed_added_weakened']==[0,0,0]
assert t['closure_routes']=={'extraction bridge':1,'extraction':27,'P6 gate':8,'axiom diagnostic':1}
assert t['candidate_closure_imports']=={'candidate':29,'neither':8}
assert t['all_row_imports']=={'research':160,'neither':112,'candidate':135}
assert t['open_dependencies']=={'b':55,'d':22,'a':10,'c':6}
manifest=json.loads((P/'manifest.json').read_text());idx={(x['ref'],x['path']):x for x in manifest}
for x in manifest:
 assert x['path'] and x['revision']==pins['revisions'][x['ref']]
 raw=(P/x['snapshot']).read_bytes();assert hashlib.sha256(raw).hexdigest()==x['sha256']
 assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==x['blob']
for a in json.loads((P/'definition-audit5.json').read_text()):
 for x in a['sources']:assert idx[x['ref'],x['path']]['sha256']==x['sha256']
assert all(x['found'] for x in json.loads((P/'evidence-audit5.json').read_text()))
assert all(x['edges_valid'] for x in json.loads((P/'wire-audit5.json').read_text()))
md=(B/'ROWS5.md').read_text();assert len(re.findall(r'^\|V',md,re.M))==407
rs=json.loads((P/'receipts.json').read_text());actual=[r for r in rs if r['compiler_invoked']];refused=[r for r in rs if not r['compiler_invoked']]
assert len(actual)==20 and len(refused)==14 and len({r['attempt'] for r in rs})==34
assert min(r['attempt'] for r in rs)==54200 and max(r['attempt'] for r in rs)==54233
assert collections.Counter(r['exit'] for r in actual)=={'0':10,'1':10}
for r in actual:
 assert all(r[k] is not None for k in ['wall','peak_RSS_KiB','swap','source_revision','source_sha256','dependency_fingerprint'])
 assert r['swap']=='0' and r['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=128,Lean_M=7000)
 if r['exit']=='0':assert r['shared_source_matches_pinned'] and r['axioms'] and not r['errors']
 text=(P/r['log']).read_text()
 if r['exit']=='0':assert 'sorryAx' not in text
for r in refused:assert 'already sent in env J' in (P/f"launcher-{r['attempt']}.log").read_text()
for c in json.loads((P/'checks.json').read_text()):
 raw=(P/c['source']).read_bytes();assert hashlib.sha256(raw).hexdigest()==c['sha256']
 assert c['module'].startswith('PV_Ledger_')
 assert all(l.startswith(('import ','set_option pp.proofs false','#check ','#print ')) for l in raw.decode().splitlines())
base=pins['worktree_base'];before=subprocess.check_output(['git','show',base+':design/PRIVACY-LEDGER-20261026.md']).decode();now=Path('design/PRIVACY-LEDGER-20261026.md').read_text()
assert now.startswith(before) and now.count('## Recount 5 2026-10-27 (B)')==1
packet=Path('design/PV-OWNER-PACKET-20261027.md').read_text();assert len(re.findall(r'^\d\. \*\*',packet,re.M))==7
assert len(packet.split())<700
allowed=('design/PRIVACY-LEDGER-20261026.md','design/PV-OWNER-PACKET-20261027.md','evidence/privacy-recount-20261026/ROWS5.md','evidence/privacy-recount-20261026/recount5/')
changed=subprocess.check_output(['git','diff','--name-only',base]).decode().splitlines()
assert all(p.startswith(allowed) for p in changed),changed
out=dict(result='PASS',rows=407,source_records=len(manifest),open=93,candidate_closed=37,Lean_invocations=20,Lean_passed=10,Lean_failed=10,duplicate_refusals=14,Kani=0,proofs=0,premises_removed_added_weakened=[0,0,0],max_peak_RSS_KiB=max(int(r['peak_RSS_KiB']) for r in actual),swaps=0,source_revision=pins['worktree_base'],target='not yet established')
(P/'validation5.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
