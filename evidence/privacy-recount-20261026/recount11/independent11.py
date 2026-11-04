from audit11 import *
manifest.update({x['ref']+':'+x['path']:x for x in json.loads((P/'manifest.json').read_text())})
def get(k,p):
 s=txt(k,p);assert s is not None,(k,p);return s
def obj(k,p):return json.loads(get(k,p))
def source(n):return get('rw','docs/research/v8-r0-zk-20261009/lean/R1Z/'+n+'.lean')
allowed={'propext','Classical.choice','Quot.sound'}; out={};receipts=[]
def receipt(k,p):
 x=obj(k,p)
 for key in ['target','exit','wall','peak_rss_kib','swap','source_revision']:assert key in x,(p,key)
 assert x['exit']==0 and int(x['swap'])==0,p
 assert 'axioms' in x or 'print_axioms' in x,p
 pre=p.rsplit('/',1)[0]
 for name in ['admission-launch.json','admission-barrier.json']:
  a=read(k,pre+'/'+name)
  if a is not None: assert json.loads(a)['allowed'] is True,(p,name)
 receipts.append({'ref':k,'path':p,'receipt':x,'axioms_kind':'SUMMARY-BASED unless separately identified raw NEP target'})
 return x
for id,th,folder in [('V233','consumed_instance','pv-rdcd5-20261101'),('V236','op216_instance','pv-rdcd5-20261101'),('V197','parser_instance','pv-rdcd7-20261102')]:
 a=obj('rw','evidence/'+folder+'/'+id+'-ASSOCIATION.json');module_name='PV_RDCD5_'+id+('Restored' if id=='V197' else '')
 s=source(module_name);assert 'theorem '+th in s
 sig=s[s.index('theorem '+th):].split(' := by')[0]
 assert 'Result' in s or id=='V233'
 bind=obj('rw','evidence/'+folder+'/'+id.lower()+'-source-bindings.json')
 out[id]={'disposition':'CONFIRM qualified restoration','theorem':'R1Z.'+module_name+'.'+th,'full_statement':sig,'association':a,'binding_sha256':hashlib.sha256(json.dumps(bind,sort_keys=True).encode()).hexdigest(),'evidence_class':'own-1/k-prime source-structural plus complete Result/typed Lean transport; finite historical native validation only; V370 retained','endpoint_removals':0}
 for name in ['focused_receipt','coherence_receipt','focused_transport_receipt','restoration_receipt']:
  if name in a:receipt('rw','evidence/'+folder+'/'+a[name])
 if id=='V197':
  for name in ['coherence','raw_summary_audit','focused','single_frozen_manifest']:receipt('rw','evidence/'+folder+'/'+a['release_gates'][name])
# Preserve exact order and late panic; no artificial length16 domain.
b=source('PV_RDCD4_BytesSource');range_source=source('PV_RDCD5_ParserRange');parser=source('PV_RDCD5_ParserErrors')
assert b.count('PV_RDCD5_ParserRange.index')==3 and 'else fail .panic' in range_source
assert b.index('match c0 with')<b.index('index bytes 8 16')
assert 'carrier_agreement' in parser and 'carrier_mismatch' not in parser
checks=obj('rw','evidence/pv-rdcd7-20261102/CONSUMER-RECHECKS.json')
for c in checks['focused']:
 s=source(c['consumer']);assert hashlib.sha256(s.encode()).hexdigest()==c['source_sha256'],c['consumer']
 assert c['status']=='PASS'
 for p in c['receipts']:
  rr=receipt('rw','evidence/pv-rdcd7-20261102/'+p);assert rr['source_sha256']==c['source_sha256']
for c in checks['unchanged']+checks['audit_query_projections']:
 assert hashlib.sha256(source(c['consumer']).encode()).hexdigest()==c['source_sha256'],c['consumer']
# Independently enumerate actual current references at every captured pin.
scans=[]
for k,rev in revs.items():
 cmd=['git','grep','-n','-E','PV_RDCD[45]_(BytesSource|ParserWindows|ParserFlat|ParserErrors|V197)|PV_RDCD4_SliceRange194',rev,'--','*.lean','*.py','*.rs','*.sh']
 r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE);assert r.returncode in [0,1]
 data=r.stdout;name='consumer-scan-'+k+'.txt';(P/name).write_bytes(data)
 scans.append({'ref':k,'revision':rev,'command':cmd,'exit':r.returncode,'sha256':hashlib.sha256(data).hexdigest(),'lines':len(data.splitlines()),'file':name})
raw=obj('rw','evidence/pv-rdcd7-20261102/RAW-AUDIT-SUMMARY.json');assert raw['root_count']==51
for x in raw['roots']:assert x['equal'] and set(x['walked_axioms'])<=allowed
out['V197_consumers']={'focused_count':len(checks['focused']),'checks':checks,'scans':scans,'raw_audit':raw,'finding':'wrong-kind dependent local short_failure and old diagnostic/replay corrected explicitly; no restored row used wrong kind; bounded V236 helper unchanged','historical_counterexample':'recount10 and rdcd7 BEFORE-sources preserve old panic/arrayOutOfBounds mismatch; no deployed bug inferred'}
# Typed bodies, no singleton fold / additional success assumption.
assert '(input : Slice U8) (origin : Nat)' in source('PV_RDCD5_V233')
assert 'typed_roundtrip' in source('PV_RDCD5_V233') and 'hp : self.buffer.pos.val < 64' in source('PV_RDCD5_V236')
for n in [78297,78298,78299]:receipt('rw',f'evidence/pv-rdcd5-20261101/lean-{n}/receipt.json')
# K-3: predecessor305 observations, overlay final scoped D592 statuses.
credits=json.loads(lzma.decompress(read('k3scan','evidence/pv-k3scan-20261101/CREDITS.json.xz')));cb={x['credit_id']:x for x in credits}
changes=obj('k3scan','evidence/pv-k3scan3-20261104/CREDITS.json')
for x in changes:cb[x['credit']]['final_status']=x['status']
counts=dict(collections.Counter(c['final_status'] for c in credits));assert counts=={'SUSPENDED':195,'UNAFFECTED':81,'RESTORED':26,'WITHDRAWN':3}
pairs=obj('k3scan','evidence/pv-k3scan3-20261104/PAIRS.json');pair_records=[]
for q in pairs:
 a=obj('k3scan','evidence/pv-k3scan3-20261104/host/'+q['positive']+'/receipt.json');z=obj('k3scan','evidence/pv-k3scan3-20261104/host/'+q['control']+'/receipt.json')
 assert a['exit_status']==0 and z['exit_status']!=0 and z['negative_control'] and q['selected_closure_unchanged']
 def h(x):return x['command'][x['command'].index('--harness')+1]
 assert h(a)==h(z)==q['harness']
 for run in [q['positive'],q['control']]:
  pre='evidence/pv-k3scan3-20261104/host/'+run+'/'
  for p in ['admission.json','barrier.json']:assert obj('k3scan',pre+p)['allowed'] is True
  r=obj('k3scan',pre+'receipt.json');assert r['caps']=={'MemoryHigh':'6G','MemoryMax':'8G','MemorySwapMax':0,'TasksMax':64};assert r['swap']==0
 pair_records.append({'pair':q,'positive_receipt':a,'control_receipt':z})
for p in tree('k3scan'):
 if p.startswith('evidence/pv-k3scan3-20261104/caller/') and p.endswith('.rs'):
  s=get('k3scan',p);assert not re.search(r'\bstatic\s+mut\b|thread_local!',s),p
roll=obj('k3scan','evidence/pv-k3scan-20261101/K3-ROWS.json')['rows']
for r in roll:
 assert not r['depends_on_still_suspended_credit'] and not r['suspended_current_support']
 for c in r['current_kani_support']:assert cb[c]['final_status'] in ['RESTORED','UNAFFECTED']
(P/'k3-audit11.json').write_text(json.dumps({'counts':counts,'changes':changes,'pairs':pair_records,'current_support_rows':roll,'no_current_support_suspended':True,'C156':'SUSPENDED despite passing local memo/caller checks: full-raw mul child/frame/G bridge missing','limits':'K-3 clearance only; new std transfer withheld, K-1/K-2/compiler/native/world restrictions retained. K3-ROWS old V233 text superseded by independent rdcd restoration.'},indent=1)+'\n')
# User client adoption: sources, final executable, every gate and independent timing arithmetic.
up='evidence/pv-uc5-20261103/';g=obj('uc',up+'gate-status.json');build=obj('uc',up+'final-build.json');sha=g['client']['sha256']
assert sha=='fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558' and build['binaries']['user_client']['sha256']==sha
for p in ['native91106','native91108','native91109','native91110','lean91097','lean91098']:receipt('uc',up+p+'/receipt.json')
rt=obj('uc',up+'runtime-final/summary.json');assert rt['client_sha256']==sha and rt['no_core_file'] and rt['post_secret_panic_no_core'] and rt['helper_dumpable']==0
assert len(rt['fd_controls'])==8 and all(c['stdout_bytes']==0 and c['stderr_literal'] for c in rt['fd_controls'])
diff=obj('uc',up+'differential/summary.json');assert diff['passed'] and diff['pairs']==100 and diff['fully_executed_prover_calls']==200
secret=obj('uc',up+'differential/secret-gate.json');rawuc=obj('uc',up+'nep/summary.json');assert rawuc['status']=='PASS' and len(rawuc['rows'])==8
for r in rawuc['rows']:assert r['equal'] and set(r['walked_axioms'])<=allowed
assert rawuc['rows'][0]['reachable_constants']==5280
main=get('uc','tools/r1-cost-probe/src/bin/user_client.rs');diag=get('uc','tools/r1-cost-probe/src/bin/user_client/diagnostics.rs');wallet=get('uc','tools/r1-cost-probe/src/bin/user_client/wallet.rs');plan=get('uc','tools/r1-cost-probe/src/bin/user_client/plan.rs')
assert 'fn main(){\n diagnostics::initialize();' in main
assert 'prctl(4, 0usize' in diag and 'setrlimit(4, &zero)' in diag
assert 'target.dev()!=metadata.dev() || target.ino()!=metadata.ino()' in wallet and 'file_type().is_fifo()' in wallet and 'pub const WIDTH:usize=212' in wallet
assert 'wallet::return_record' in plan and 'wallet::retain' not in plan and 'pub fn retain' not in wallet
# Verify candidate adoption identity for every changed client file; no crates/programs difference at adoption.
changed=git('diff','--name-only','8897074612^1','8897074612','--','tools/r1-cost-probe').decode().splitlines()
for p in changed:assert read('rw',p)==read('uc',p),p
assert not git('diff','--name-only','8897074612^1','8897074612','--','crates','programs').strip()
host=json.loads(lzma.decompress((P/'host-timing/inputs.json.xz').read_bytes()));hs=lambda p:json.loads(host[p])
prefix='final-gates/timing-d561/native91120/';timing=hs(prefix+'summary.json');bp=hs(prefix+'binary-pins.json');assert bp['draft']['sha256']==sha and timing['pairs']==10
import statistics
for r in timing['summary']:
 vals=r['groups']['all']['values'];med={k:statistics.median(v) for k,v in vals.items()};assert all(len(v)==10 for v in vals.values());ratio=med['draft']/med['baseline'];assert ratio<=1.10 and med['draft']<15 and r['verdict']=='PASS' and ratio==r['groups']['all']['ratio']
for p in ['native91120/admission-before.json','native91120/admission-launch.json','native91120/admission-barrier.json']:assert hs(p)['allowed'] is True
assert host['native91120/done-status.txt'].strip()=='0'
out['client']={'disposition':'CONFIRM ADOPTED at 8897074612 and candidate d4ed1ba89f','client_sha256':sha,'source_paths':changed,'gate_status':g,'runtime':rt,'differential':diff,'secret_search':secret,'raw_audit':rawuc,'timing':timing['summary'],'timing_receipt':{'target':'python3 timing-window.py via capped native91120','exit':0,'wall':'9:47.26','peak_rss_kib':598864,'swap':0,'source_revision':'025621b1e6','axioms':'N/A native timing','raw_inputs':'host-timing/inputs.json.xz'},'owner_decisions':'D524 client scope, D575(A) startup non-dumpable/core0, D576(B) raw212-byte caller pipe, no secrets on disk; no new T','limits':'1000 old differential pairs remain attributed to uc3; final100 pairs bind final binary. Finite raw-field search is not noninterference; decoder trace is finite; parametric entry22 carriers/105 ops still needs native effects. Client-release half met; V396 native integration remains OPEN.'}
# Coherent composition status is a three-part gate, never scan-only credit.
ev=obj('evhc','evidence/pv-evhc8-20261104/RESULT.json');assert ev['steps'][0]['exit_status']==0 and ev['steps'][1]['exit_status']==0 and ev['steps'][2]['exit_status']!=0 and not ev['composition_counts']
out['composition']={'result':ev,'disposition':'92060 does NOT count: compile+zero-dangling scan pass; raw driver fails before walk. No coherent joint non-vacuity/release audit credited; evhc9 preflight is not aggregation.'}
out['structural_status_notes']={'D589':'Pure Result with fixed ExternalFuns cannot represent advancing stateful OS answers. A constant callback record does not model retry/redraw/threads/world effects. Root mismatch confirmed; not a counted row.', 'l3-2':'Five source-level projections native events/fileTrace/countTrace/timeTrace/oraclePrefix must arise from one source world run, independently of physical frame interpretation.', 'L3':'ActualEntropyEntryPrefix source-to-machine carrier (V370/L3), unconstructed/unproved. Binary-structural da36d6aa evidence is historical scoped evidence; new fc8808 adopted client needs binding/refresh. OWNER heap is not FRAME stack.', 'stx':'Pinned route B has fixed-handler no-regression machine/lifts,42 raw roots; no complete source_entry_world or five deployed projections. No row restoration.'}
(P/'independent-audit11.json').write_text(json.dumps(out,indent=1)+'\n');(P/'receipt-audit11.json').write_text(json.dumps(receipts,indent=1)+'\n');save();print('PASS: qualified restorations,15 focused consumer hashes/receipts,51 raw roots, K3',counts,'client gates and timing; receipts',len(receipts))
