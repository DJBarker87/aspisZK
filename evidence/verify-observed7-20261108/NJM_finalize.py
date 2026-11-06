"""Build the additive row packet only from current sources and successful gates."""
from pathlib import Path
import json,lzma,hashlib,subprocess,copy
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads((E/p).read_text())
def write(p,v):(E/p).write_text(json.dumps(v,indent=2)+'\n')
basepath=E.parent/'ledger14-20261108/NJK_LEDGER.json.xz'
base=json.loads(lzma.open(basepath).read());rows={r['row']:r for r in base['rows']}
modules=read('NJM_MODULES.json');groups=read('NJM_AUDIT_ROOTS.json')['groups'];roots=sum(groups,[])
assert len(modules)==35 and len(roots)==77 and len(set(roots))==77
for m in modules:
 assert sha(E/(m['module']+'.lean'))==m['sha256']
 r=read(m['attempt']+'/receipt.json')
 assert r['exit_status']==0 and r['source_hashes']['NJM_generated/'+m['module']+'.lean']==m['sha256']
 assert not any('sorryAx' in s for s in r['print_axioms'])
 assert '#print axioms' in (E/(m['module']+'.lean')).read_text()
gates=[]
for a,mode,name in [('NJM_L097','scan','scan'),('NJM_L092','fixtures','fixtures'),*[(f'NJM_L{93+i:03}',f'batch{i}',f'proof{i}') for i in range(4)]]:
 r=read(a+'/receipt.json');q=read(f'NJM_audit/{mode}/{name}.json')
 assert r['exit_status']==q['exit_status']==0 and q['policy_pass']
 gates.append(dict(attempt=a,mode=mode,receipt=a+'/receipt.json',raw=f'NJM_audit/{mode}/{name}.json',wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
scan=[json.loads(l) for l in (E/'NJM_LOADED_scan.jsonl').read_text().splitlines()]
assert len(scan)==15630 and all(x['imports_match'] and not x['dangling'] and not x['duplicate_owners'] for x in scan)
raw=sum([read(f'NJM_audit/batch{i}/proof{i}.json')['results'] for i in range(4)],[])
assert [r['root'] for r in raw]==roots
assert all(r['equal'] and r['walked_axioms']==r['collect_axioms'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
assert read('NJM_L086/receipt.json')['exit_status']==0
assert read('NJM_E001/receipt.json')['exit_status']!=0 and read('NJM_EXTRACTION_PINS.json')['aeneas_exit']==2
native=read('NJM_NATIVE_RESULTS.json');assert native['kani_scopes']==11 and not native['row129_closed']
assert native['current_data_pair']==['NJM_K011','NJM_K012']
for n,code in [('NJM_K011',0),('NJM_K012',1),('NJM_K006',0),('NJM_K007',1),('NJM_K008',1)]:assert read(n+'/receipt.json')['exit_status']==code
functions=[]
for num,root,pairs,domain in [
 (133,'round',[['NIX_K073','NIX_K074'],['NIX_K075','NIX_K076']], 'Every actual ten-site round index; SAME parsed record/901-byte row, polynomial, boundary, semantic reply, all Result/effect/native args/post/frame cases; rejected parse is private-callee non-entry'),
 (134,'rounds',[['NJG_K016','NJG_K017'],['NJG_K018','NJG_K019']], 'Original ten-call order at every SAME returned carry; concrete133 child packet, canonical active prefix, immutable hash frame, all abort prefixes; only reviewed universally quantified native Cut is a Prop premise'),
 (142,'circle',[['NIX_K049','NIX_K050']], 'Every SAME actual parsed record slot; concrete sampler dictionary and dispatch, both valid circle tags and invalid tags, all reply/error/abort/effect/transcript/frame cases; framed bound derived internally')]:
 r=rows[f'TX1:{num}'];functions.append(dict(rows=[r['row']],function=r['function'],frozen_body_sha256=r['frozen_body_sha256'],obligation_statement_hash=r['obligation_statement_hash'],route='(y)/(aq)(5) direct P6 hybrid, complete concrete child/cut installation',root_domain=domain,native_pairs=pairs,lean_roots=['AspisR1.NJM_InvocationRoots.'+root],complete_carrier=True,premise_policy='Root inputs, actual private invocation domain, existing native-cut/tool/runtime interpretations only; no caller success, endpoint, child law, Run or arbitrary operation dictionary hypothesis',trust='P6/D188 option A RECLASSIFICATION; existing Std/allocator/runtime trust retained, none added/removed'))
packet=dict(frozen_revision=base['frozen_revision'],headline=base['headline'],functions=functions,root137_closed=False,finish136_closed=False,prepare_op9_instantiated=False,admission='PASS local combined import, NFX coherence and ax2 raw checks; credit waits for next ledger gate',status='CLOSED candidates within recorded per-row invocation domains; not an authoritative ledger update',validation='NJM_VALIDATION.json')
write('NJM_CLOSED.json',packet)
write('NJM_LEDGER_DELTA.json',dict(baseline='evidence/ledger14-20261108/NJK_LEDGER.json.xz',baseline_sha256=sha(basepath),baseline_counts={'CLOSED':438,'QUALIFIED':0,'OPEN':161},updates=[dict(row=x['rows'][0],previous='OPEN',proposed='CLOSED',packet='NJM_CLOSED.json',lean_roots=x['lean_roots']) for x in functions],authoritative_ledger_changed=False,credit='PENDING next ledger gate',untouched_open=['TX1:129','TX1:136','TX1:256'],security_target_established=False))
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NJM_[LKE][0-9][0-9][0-9]/receipt.json'))]
counts={k:sum(r['attempt'][4]==k for r in receipts) for k in 'LKE'}
assert counts['L']<=120 and counts['K']<=70 and counts['E']==1
write('NJM_AUDIT.json',dict(status='PASS local candidate gates; next ledger admission pending',headline=base['headline'],frozen_revision=base['frozen_revision'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,source_hash_manifest='NJM_MODULES.json',statement_inventory='NJM_PRINTED_ROOTS.md',modules=35,raw_roots=77,standard_axioms=['propext','Classical.choice','Quot.sound'],full_combined_compiles=['NJM_L063','NJM_L086'],coherence_scan_attempts=['NJM_L091','NJM_L097'],scan_first_failure='Owned expected-import manifest omitted implicit Init on all36 new modules; no dangling or incompatible declarations. Generator fixed, unchanged stricter checker passed L097.',full_raw_campaigns=1,gates=gates,resource_limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64,Lean_M=7000,simultaneous_scopes=1),budget=dict(limit={'L':120,'K':70,'E':1},submitted_scopes=counts,prelaunch_failures=['NJM_L084'],unused_reason='NJM_REMAINING.md'),native='NJM_NATIVE_RESULTS.json',export='NJM_EXPORT.json',resolved_libraries='NJM_RESOLVED_OBJECTS.json',consumer='NJM_CONSUMER_CHECK.json',exclusions='NJM_EXCLUDED_DRAFTS.json',trust_added=[],trust_removed=[],trust_reclassification='P6/D188 option A',rows129_136_closed=False,security_target_established=False))
def validate(p):
 assert p['frozen_revision']==base['frozen_revision'] and p['headline']==base['headline']
 assert not p['finish136_closed'] and not p['root137_closed'] and not p['prepare_op9_instantiated']
 assert [f['rows'] for f in p['functions']]==[['TX1:133'],['TX1:134'],['TX1:142']]
 for f,expected in zip(p['functions'],functions):
  assert f==expected
validate(packet);controls=[]
mutations=[('unproved129',lambda p:p['functions'].append(dict(rows=['TX1:129']))),('finish136',lambda p:p.update(finish136_closed=True)),('wrong_headline',lambda p:p.update(headline='other')),('tampered_root',lambda p:p['functions'][0].update(lean_roots=['other'])),('wrong_source',lambda p:p['functions'][1].update(frozen_body_sha256='0'*64)),('added_trust',lambda p:p['functions'][2].update(trust='new trust'))]
for name,mutate in mutations:
 p=copy.deepcopy(packet);mutate(p)
 try:validate(p)
 except AssertionError:controls.append(dict(control=name,rejected=True))
 else:raise AssertionError('Control accepted: '+name)
assert not subprocess.run(['git','diff','--quiet',base['frozen_revision'],'--','crates','programs','Cargo.lock']).returncode
large=[str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
write('NJM_VALIDATION.json',dict(status='PASS',mutation_controls=controls,current_sources=True,raw_standard_only=True,coherence=True,frozen_shipping_identical=True,files_over20MB=large,authoritative_ledger_unchanged=True,security_target_established=False))
print(json.dumps(dict(validation='PASS',candidate_rows=[133,134,142],raw_roots=len(raw),scopes=counts,next_ledger_credit_pending=True)))
