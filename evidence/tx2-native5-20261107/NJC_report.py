from pathlib import Path
import json,hashlib,lzma,re,subprocess
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=1)+'\n')
receipts=[]
for p in sorted(E.glob('NJC_[KLE][0-9][0-9][0-9]/receipt.json')):
 r=load(p);a=r['attempt'];ad=load(E/(a+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},(a,r['limits'])
 assert str(r['swaps'])=='0',a
 assert r['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-tx2-native5-20261107/NJC_target',a
 receipts.append(r)
counts={k:sum(r['attempt'].startswith('NJC_'+k) for r in receipts) for k in ['K','L','E']};assert counts['K']==80 and counts['E']==1 and counts['L']<=100,counts
allowed={'propext','Classical.choice','Quot.sound'}
modules=load(E/'NJC_MODULES.json')['selected']
for m in modules:
 assert sha(E/(m['module']+'.lean'))==m['source_sha256'],m
 r=load(E/m['receipt']);assert r['exit_status']==0
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   q=re.search(r'\[([^]]*)\]',line);assert q and all(a.strip() in allowed for a in q[1].split(',')),line
roots=[x for g in load(E/'NJC_AUDIT_ROOTS.json')['groups'] for x in g]
proofs=[]
for p in sorted((E/'NJC_audit/all').glob('proof*.json')):
 x=load(p);assert x['exit_status']==0
 for row in x['results']:
  assert row['equal'] and set(row['collect_axioms'])<=allowed and set(row['walked_axioms'])<=allowed,row
  proofs.append(row)
assert {r['root'] for r in proofs}==set(roots) and len(proofs)==len(roots),(len(proofs),len(roots))
assert load(E/'NJC_L093/NJC_ProofDriver_BINARY_PIN.json')==load(E/'NJC_L094/NJC_ProofDriver_BINARY_PIN.json')
fixture=load(E/'NJC_audit/fixtures/fixtures.json');assert fixture['exit_status']==0 and len(fixture['results'])==8 and all(r['equal'] for r in fixture['results'])
loaded=[json.loads(s) for s in (E/'NJC_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in loaded)
assert load(E/'NJC_L095/receipt.json')['exit_status']==0
assert 'NFN_SCAN_ZERO_DANGLING' in (E/'NJC_audit/scan/scan.log').read_text()
assert load(E/'NJC_SOURCE_VERIFICATION.json')['status']=='PASS' and load(E/'NJC_CLEANUP.json')['status']=='PASS'
graphs=[]
for p in sorted(E.glob('NJC_K[0-9][0-9][0-9]-graph-check.json')):
 a=p.name.removesuffix('-graph-check.json');x=load(p);assert x['graph_matches_frozen'] and not x['edge_errors'] and not x['new_package_tuples'],a
 lock=load(E/(a+'-lock-check.json'));assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
 assert not load(E/(a+'-source-check.json'))['errors'],a
 graphs.append(dict(attempt=a,graph_sha256=x['graph_sha256'],lock_sha256=lock['after']))
assert len(graphs)==79 # K001 stops at frozen-source preflight, before any Kani launch.
mat=load(E/'NJC_NATIVE_MATRIX.json')
for row in mat:
 if not row.get('negative') or not row.get('rename'):continue
 for key,exitcode,marker in [('positive',0,'VERIFICATION:- SUCCESSFUL'),('negative',1,'VERIFICATION:- FAILED'),('rename',0,'VERIFICATION:- SUCCESSFUL')]:
  a=row[key];r=load(E/a/'receipt.json');assert r['exit_status']==exitcode and marker in (E/a/'stdout.log').read_text(),(row['family'],key)
for p in E.rglob('*'):
 assert p.name!='__pycache__',p
 if p.is_file():assert p.stat().st_size<=20000000,(str(p),p.stat().st_size)
start=subprocess.check_output(['git','rev-parse','6911b6ee605^'],text=True).strip()
changed=subprocess.check_output(['git','diff','--name-only',start,'HEAD'],text=True).splitlines();assert all(n.startswith('evidence/tx2-native5-20261107/') for n in changed)
baseRaw=lzma.decompress((E.parent/'ledger13-20261107/NIU_LEDGER.json.xz').read_bytes());base=json.loads(baseRaw);assert base['counts']=={'CLOSED':432,'OPEN':167} and len(base['rows'])==599,base['counts']
final_source=load(E/'NJC_L090/receipt.json')['source_revision']
resource=[]
for r in receipts:
 resource.append({k:r.get(k) for k in ['attempt','kind','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_tree_dirty','source_hashes','print_axioms','limits','cgroup','cgroup_memory_peak_bytes']})
raw=json.dumps(resource,separators=(',',':')).encode();(E/'NJC_RELEASE_RESULTS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NJC_RELEASE_RESULTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
# These are complete emitted child Results installed at literal call sites.
# Neither local evidence nor this packet performs the authoritative next ledger gate.
candidates=[]
for rid,root,installation,domain in [('TX2:126','NJC_ValidatePort.source','NJC_ValidateCalls.resume','every Array U32 22; no acceptance, uniqueness, or range premise'),('TX2:107','NJC_ConcreteUnwrap.clause','NJC_RawCalls.resume','complete emitted raw body on all represented pre-states; native windows N4/16/32 plus symbolic byte/frame lift; final native caller-domain review retained')]:
 row=next(r for r in base['rows'] if r['row']==rid)
 candidates.append(dict(row=rid,function=row['function'],frozen_body_sha256=row['frozen_body_sha256'],complete_emitted_result=root,same_argument_installation=installation,domain=domain,status='COMPLETE_EMITTED_CHILD_RESULT_NEXT_LEDGER_REVIEW',native_ledger_credit=False,new_trust_rows=[]))
write('NJC_CLOSED.json',dict(schema_version=1,headline='AspisR1.RPx_Deployed.deployed',target='TX2:065',status='OPEN',security_target_established=False,admitted_rows=[],candidate_child_results=candidates,credit='Waits for next authoritative ledger gate; no current native row/count promotion',remaining='NJC_REMAINING.md'))
write('NJC_LEDGER_DELTA.json',dict(schema_version=1,baseline='evidence/ledger13-20261107/NIU_LEDGER.json.xz',baseline_uncompressed_sha256=hashlib.sha256(baseRaw).hexdigest(),baseline_counts=base['counts'],promotions=[],demotions=[],row_changes=[],result_counts=base['counts'],target=dict(row='TX2:065',before='OPEN',after='OPEN'),candidate_child_results=[r['row'] for r in candidates],next_ledger_gate_required=True,security_target_established=False,new_trust_rows=[]))
write('NJC_AUDIT.json',dict(schema_version=1,status='PASS_COMPONENT_AUDIT_PARENT_OPEN',headline='AspisR1.RPx_Deployed.deployed',final_source_revision=final_source,budget=dict(used=counts,limits={'K':80,'L':100,'E':1}),selected_modules=len(modules),raw_roots=len(roots),raw_axioms=sorted(allowed),raw_results=proofs,fixtures=dict(receipt='NJC_L093/receipt.json',same_binary_receipt='NJC_L094/NJC_ProofDriver_BINARY_PIN.json',count=8,passed=True),combined=dict(receipt='NJC_L090/receipt.json',includes=['NGK_COMBINED_IMPORT','NIU_COMBINED_IMPORT','NIY_COMBINED_IMPORT','AspisR1.RPx_Deployed.deployed']),nfx_scan=dict(receipt='NJC_L095/receipt.json',exit_status=0,modules=len(loaded),declarations=sum(r['declarations']for r in loaded),dangling=0,duplicate_owners=0,import_mismatches=0),native_graph_checks=graphs,source_and_retention='NJC_SOURCE_VERIFICATION.json',closure_pins='NJC_CLOSURE_PINS.json.xz',export='NJC_EXPORT.json',cleanup='NJC_CLEANUP.json',formal_resources='NJC_RELEASE_RESULTS.json.xz',no_shipped_changes=True,ELF_rebuild='No trigger: all Rust harness changes are scratch-only patch inputs; inherited release pins, no fresh rebuild claim',positive_native_root_available=False,hypothesis_audit=dict(statement='NJC_L089/stdout.log #print NJC_OrderedCalls.parent',ordinary_inputs=['d','public','proof','checkpoint','hash'],release_observer='none',unbound_parameters=['base : VTop_Stages.Ops','reserved : Bool not yet associated to actual Reservation'],extra_child_result_hypotheses=[],disposition='Partial dictionary substitution is not a positive actual-native root. Additional fields/producers are OPEN.'),new_trust_rows=[],security_target_established=False))
x=load(E/'NJC_CLOSED.json');x.update(closed_rows=[],closed_edges=[],model_transport=['NJC_ClosedCalls','NJC_ValidateCalls','NJC_ConcreteUnwrap','NJC_RawCalls','NJC_OrderedCalls'],model_transport_status='Selected complete child clauses installed; positive native root OPEN',native_facets_are_not_NDT_rows=True);write('NJC_CLOSED.json',x)
x=load(E/'NJC_LEDGER_DELTA.json');x.update(baseline_compressed_sha256=sha(E.parent/'ledger13-20261107/NIU_LEDGER.json.xz'),headline='AspisR1.RPx_Deployed.deployed',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',rows=[],edges=[],counts_before=base['counts'],counts_after=base['counts'],trust_rows_added=[],trust_rows_removed=[]);write('NJC_LEDGER_DELTA.json',x)
x=load(E/'NJC_AUDIT.json');x.update(raw_ax2=dict(status='PASS',receipt='NJC_L094/receipt.json',roots=len(roots),same_binary_fixtures=8,standard_only=True),failed_attempt_objects_excluded=True,native_rows_promoted=0,tool_pins='NJC_TOOL_PINS.json',walker_pins='NJC_WALKER_PIN.json');write('NJC_AUDIT.json',x)
print(json.dumps(dict(status='PASS',budget=counts,modules=len(modules),roots=len(roots),scan_modules=len(loaded),target='OPEN')))
