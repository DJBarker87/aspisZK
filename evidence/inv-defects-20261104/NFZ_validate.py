"""Validate the blocked result and reject mutations at the review boundary."""
import pathlib,json,lzma,hashlib,importlib.util,sys,copy,collections
sys.dont_write_bytecode=True
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
def J(n):return json.loads((E/n).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
sp=importlib.util.spec_from_file_location('NFZ_inventory',E/'NFZ_inventory.py');inv=importlib.util.module_from_spec(sp);sp.loader.exec_module(inv)
o=J('NFZ_OVERLAY.json');edgebytes=(E/'NFZ_EDGES.json').read_bytes();edges=json.loads(edgebytes)
for k in ['producer','canonical_producer','slice_tool','baseline']:
 p=o[k];assert sha(inv.read(p['path']))==p['sha256'],k
for p in o['inventory_inputs']:assert sha(inv.read(p['path']))==p['sha256']
assert not edges and o['review_status']=='BLOCKED_MISSING_COMPILER_EVIDENCE'
base=json.loads(lzma.open(R/o['baseline']['path']).read());admitted=json.loads(lzma.open(E/'NFZ_ADMITTED_LEDGER.json.xz').read())
assert base==admitted==inv.apply(base,o,edgebytes)
assert len(admitted['rows'])==587 and len({r['row'] for r in admitted['rows']})==587
assert J('NFZ_COVERAGE.json')['counts']==dict(total=587,covered=585,outside=2,D_functions=295,D_edges=448,D_rows=343)
assert J('NFZ_LEDGER_DELTA.json')['before']==J('NFZ_LEDGER_DELTA.json')['after']==base['coverage']
assert J('NFZ_INDEPENDENT_CHECK.json')['agrees'] is True and J('NFZ_INDEPENDENT_CHECK.json')['compiler_independent_check_satisfied'] is False
raw=lzma.decompress((E/'NFZ_FROZEN_SOURCE.json.xz').read_bytes());assert sha(raw)==(E/'NFZ_FROZEN_SOURCE.json.sha256').read_text().strip();source=json.loads(raw);pins=J('NFZ_SOURCE_PINS.json')
assert all(sha(t.encode())==pins['files'][p] for p,t in source.items())
receipt=J('NFZ_B001/receipt.json');ad=J('NFZ_B001-admission.json')
# Host recovery retained the reservation's raw JSON; the transport record
# carries the reservation subprocess exit (ssh propagates it). Require both.
transport=[json.loads(line) for line in (E/'NFZ_TRANSPORT.jsonl').read_text().splitlines()]
assert transport[0]['exit']==0 and ad['allowed'] is True
assert json.loads((E/'NFZ_B001-admission-0.log').read_text())==ad
assert receipt['exit_status']==1 and receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} and int(receipt['swaps'])==0
for p,h in receipt['source_hashes'].items():assert sha((E/'NFZ_B001/sources'/p).read_bytes())==h
assert 'AssertionError' in (E/'NFZ_B001/stdout.log').read_text() and not J('NFZ_TOOLS_AND_LOCK.json')['target_created']
assert J('NFZ_TOOLS_AND_LOCK.json')['frozen_lock_after']==pins['files']['Cargo.lock']
assert J('NFZ_PREFLIGHT_DIAGNOSIS.json')['metadata_projection_pass'] is True
hyp=J('NFZ_HYPOTHETICAL_COVERAGE.json');assert hyp['covered_existing_rows']==587 and hyp['original_NFQ_slice_assertion_would_pass'] is False
assert hyp['slice_root_closure_growth']['Q']==['crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31']
tests=[]
def deny(name,fn):
 try:fn()
 except (AssertionError,KeyError):tests.append(dict(test=name,status='rejected'))
 else:raise AssertionError('accepted mutation: '+name)
bad=copy.deepcopy(o);bad['edge_list_sha256']='0'*64;deny('changed edge-list digest',lambda:inv.apply(base,bad,edgebytes))
bad=copy.deepcopy(o);bad['review_status']='REVIEWED';deny('unearned reviewed empty overlay',lambda:inv.apply(base,bad,edgebytes))
def edge_case(method='source',target='programs/r1-cost-probe/src/lib.rs::error'):
 edge={'from':'programs/r1-cost-probe/src/lib.rs::first_decoded','to':target,'kind':'callback','evidence':dict(path='evidence/inv-defects-20261104/NFZ_SCAN.json',sha256=sha((E/'NFZ_SCAN.json').read_bytes()),method=method,compiler_gate_passed=False)}
 b=json.dumps([edge]).encode();ov=copy.deepcopy(o);ov.update(review_status='REVIEWED',edge_list_sha256=sha(b));return ov,b
a,b=edge_case();deny('source discovery cannot admit callback',lambda:inv.apply(base,a,b))
a,b=edge_case('rustc-MIR');deny('missing successful compiler gate',lambda:inv.apply(base,a,b))
a,b=edge_case('rustc-MIR','missing::node');deny('unlisted new node cannot silently enter graph',lambda:inv.apply(base,a,b))
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
assert not list(E.rglob('__pycache__'))
report=dict(result='PASS for blocked-result consistency; NOT completion of requested compiler-backed repair',row_count=587,reviewed_edges=0,status_changes=0,coverage='585/587',tests=tests,scope_receipt={k:receipt[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']},budget=dict(scopes=1,Kani=0,Lean=0,extraction=0,typecheck_builds_started=0),no_compiler_reachability_claim=True)
(E/'NFZ_VALIDATION.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(report))
