"""Validate terminal part-3 blocked packet; passing is not edge-repair credit."""
import pathlib,json,lzma,hashlib,importlib.util,sys,copy,base64,ast
sys.dont_write_bytecode=True
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
J=lambda n:json.loads((E/n).read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
sp=importlib.util.spec_from_file_location('NFZ_inventory',E/'NFZ_inventory.py');inv=importlib.util.module_from_spec(sp);sp.loader.exec_module(inv)
o=J('NFZ_OVERLAY.json');edgebytes=(E/'NFZ_EDGES.json').read_bytes()
for k in ['producer','canonical_producer','slice_tool','baseline']:
 p=o[k];assert sha(inv.read(p['path']))==p['sha256'],k
for p in o['inventory_inputs']:assert sha(inv.read(p['path']))==p['sha256']
assert not json.loads(edgebytes) and o['review_status']=='BLOCKED_MISSING_COMPILER_EVIDENCE'
base=json.loads(lzma.open(R/o['baseline']['path']).read());after=json.loads(lzma.open(E/'NFZ_ADMITTED_LEDGER.json.xz').read())
assert after==base==inv.apply(base,o,edgebytes)
assert J('NFZ_COVERAGE.json')['counts']==dict(total=587,covered=585,outside=2,D_functions=295,D_edges=448,D_rows=343)
delta=J('NFZ_LEDGER_DELTA.json');assert delta['before']==delta['after']==base['coverage'];assert delta['QSD_regenerated']
assert not any(v['added'] or v['removed'] for v in delta['slice_membership_changes'].values())
assert not any(delta[k] for k in ['new_rows','removed_rows','status_changes','new_closed_rows'])
c=J('NFZ_CANDIDATES.json');assert len(c['candidates'])==39 and not c['complete'] and not any(x['admitted'] for x in c['candidates'])
assert sum(x['compiler_target_resolution']=='CONFIRMED_IN_CORE_BODY' for x in c['candidates'])==6
ind=J('NFZ_INDEPENDENT_CHECK.json');assert ind['core_second_MIR_agrees'] and not ind['compiler_independent_check_satisfied']
for stem in ['NFZ_FROZEN_SOURCE.json','NFZ_FROZEN_BINARY.json','NFZ_aspis_core.mir','NFZ_aspis_core.mir0','NFZ_aspis_core.hir']:
 raw=lzma.open(E/(stem+'.xz')).read();assert sha(raw)==(E/(stem+'.sha256')).read_text().strip()
for attempt,code in [('NFZ_B001',1),('NFZ_B002',101),('NFZ_B004',101),('NFZ_B003',101),('NFZ_B005',1)]:
 r=J(attempt+'/receipt.json');a=J(attempt+'-admission.json');assert a.get('allowed',a.get('reservation',{}).get('allowed')) is True
 assert r['exit_status']==code and int(r['swaps'])==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for p,h in r['source_hashes'].items():assert sha((E/attempt/'sources'/p).read_bytes())==h
assert J('NFZ_GRAPH_CHECK.json')['graph_matches_frozen'];assert J('NFZ_LOCK_CHECK.json')['unchanged']
assert J('NFZ_PAYLOAD_PREFLIGHT.json')['result']=='PASS'
assert J('NFZ_PAYLOAD_PREFLIGHT.json')['local_dry_collection']['byte_identical']
assert J('NFZ_PART2_SUMMARY.json')['scope_budget']==dict(authorized=3,used=3,remaining=0)
# Check own scripts syntactically without executing any launch or producing pycache.
for p in E.glob('NFZ_*.py'):ast.parse(p.read_text(),filename=str(p))
tests=[]
def deny(name,fn):
 try:fn()
 except (AssertionError,KeyError):tests.append(dict(test=name,status='rejected'))
 else:raise AssertionError('accepted mutation: '+name)
bad=copy.deepcopy(o);bad['edge_list_sha256']='0'*64;deny('edge digest mutation',lambda:inv.apply(base,bad,edgebytes))
bad=copy.deepcopy(o);bad['review_status']='REVIEWED';deny('unearned review',lambda:inv.apply(base,bad,edgebytes))
for method,gate,to in [('source',False,'programs/r1-cost-probe/src/lib.rs::error'),('rustc-MIR',False,'programs/r1-cost-probe/src/lib.rs::error'),('rustc-MIR',True,'absent::node')]:
 edge=dict(from_function='programs/r1-cost-probe/src/lib.rs::first_decoded',to=to,kind='callback',evidence=dict(path='evidence/inv-defects-20261104/NFZ_SCAN.json',sha256=sha((E/'NFZ_SCAN.json').read_bytes()),method=method,compiler_gate_passed=gate));edge['from']=edge.pop('from_function')
 raw=json.dumps([edge]).encode();ov=copy.deepcopy(o);ov.update(review_status='REVIEWED',edge_list_sha256=sha(raw));deny('unreviewed or missing target '+method+str(gate),lambda:inv.apply(base,ov,raw))
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
assert not list(E.rglob('__pycache__'))
r=J('NFZ_B005/receipt.json');assert r['thread_measurement']['measured_cgroup_threads_peak']==17<64
assert r['env']['CARGO_BUILD_JOBS']=='1' and r['env']['RUSTFLAGS']=='-C codegen-units=1'
assert J('NFZ_B005_FINAL_CHECK.json')['source_pins_after']
assert not (E/'NFZ_B006/receipt.json').exists()
assert J('NFZ_PART3_SUMMARY.json')['binding_stop'] is True
report=dict(part3_scopes_used=1,part3_scope2='UNUSED_BINDING_STOP',measured_peak_threads=17,result='PASS blocked-packet consistency only; requested inventory repair remains INCOMPLETE',coverage='585/587',admitted_edges=0,status_changes=0,new_rows=0,partial_core_resolutions=6,unresolved_entry_candidates=39,part2_scopes_used=3,Kani=0,Lean=0,extraction=0,tests=tests)
(E/'NFZ_VALIDATION.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(report))
