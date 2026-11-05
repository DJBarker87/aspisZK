"""Summarize retained evidence without promoting local checks to native rows."""
from pathlib import Path
from collections import Counter
import json,hashlib,re,subprocess,lzma
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen_raw=lzma.decompress((E/'NIC_FROZEN.json.xz').read_bytes());assert hashlib.sha256(frozen_raw).hexdigest()==(E/'NIC_FROZEN.json.sha256').read_text().strip()
frozen_lock_sha256=hashlib.sha256(json.loads(frozen_raw)['Cargo.lock'].encode()).hexdigest()
rs=[json.loads(l) for l in (E/'NIC_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rs)==104 and len({r['attempt'] for r in rs})==104
native=[r for r in rs if r['kind']=='kani'];assert len(native)==80
assert sum(r['kind']!='kani' for r in rs)<=60
assert sorted(r['attempt'] for r in native)==[f'NIC_K{i:03d}' for i in range(1,81)]
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for r in rs:
 assert r['limits']==limits and int(r['swaps'])==0,r['attempt']
 if str(r.get('cgroup_memory_peak_bytes','')).isdigit():assert int(r['cgroup_memory_peak_bytes'])<=8589934592
 ad=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 if r['kind']=='kani':
  assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
  graph=E/(r['attempt']+'-graph-check.json')
  # K029 stops in an own Python parse error before metadata/cargo/Kani.
  if r['attempt']=='NIC_K029':assert not graph.exists();continue
  g=json.loads(graph.read_text());assert g['graph_matches_frozen'] and g['exact_frozen_selected_graph']
  assert g['resolved_features_all_crates']
  lock=json.loads((E/(r['attempt']+'-lock-check.json')).read_text());assert lock['unchanged'] and lock['before']==lock['after']==frozen_lock_sha256
# Exact final source receipts, not failed drafts/error-recovery objects.
final={'NIC_PurityFrame':1,'NIC_AbortPrefix':2,'NIC_FieldStubs':7,'NIC_FoldDomains':8,'NIC_DriverPackets':9,'NIC_COMBINED_IMPORT':20,'NIC_ProofDriver':11,'NIC_AllocatorPrefix':19}
for module,num in final.items():
 r=json.loads((E/f'NIC_L{num:03d}'/'receipt.json').read_text());assert r['exit_status']==0
 snap=E/f'NIC_L{num:03d}'/'sources'/'NIC_generated'/(module+'.lean');assert snap.read_bytes()==(E/(module+'.lean')).read_bytes()
for p in [E/(n+'.lean') for n in final if n not in ['NIC_ProofDriver']]:
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',p.read_text().replace('#print axioms',''))
roots=json.loads((E/'NIC_audit/batch0/proof0.json').read_text())
assert roots['exit_status']==0 and len(roots['results'])==2
prior_roots=json.loads((E/'NIC_AUDIT_PRIOR16.json').read_text());assert prior_roots['exit_status']==0 and len(prior_roots['results'])==16
roots['results']=prior_roots['results']+roots['results'];assert len({r['root'] for r in roots['results']})==18
assert json.loads((E/'NIC_DRIVER_REUSE.json').read_text())['binary_identical']
standard={'propext','Classical.choice','Quot.sound'}
for row in roots['results']:assert row['equal'] and set(row['walked_axioms'])<=standard
fixtures=json.loads((E/'NIC_audit/fixtures/fixtures.json').read_text());assert fixtures['exit_status']==0 and len(fixtures['results'])==8
for i,row in enumerate(fixtures['results']):assert row['equal'] and (bool(row['walked_axioms'])==(i<4))
scan=[json.loads(l) for l in (E/'NIC_LOADED_scan.jsonl').read_text().splitlines()];assert len(scan)==13648
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
assert json.loads((E/'NIC_L023/receipt.json').read_text())['exit_status']==0
raw=lzma.decompress((E/'NIC_CLOSURE_PINS.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'NIC_CLOSURE_PINS.json.sha256').read_text().strip()
assert json.loads((E/'NIC_WALKER_PIN.json').read_text())['NFA_byte_identical']
old_pins=json.loads(lzma.decompress((E/'NIC_STAGE1_CLOSURE_PINS.json.xz').read_bytes()))['selected_objects']
new_pins=json.loads(raw)['selected_objects']
def key(r):return (r['module'],Path(r['path']).name)
old={key(r):r['sha256'] for r in old_pins};new={key(r):r['sha256'] for r in new_pins}
changed={k[0] for k in set(old)|set(new) if old.get(k)!=new.get(k)}
assert changed=={'NIC_COMBINED_IMPORT','NIC_AllocatorPrefix'},changed
(E/'NIC_PRIOR_ROOT_REUSE.json').write_text(json.dumps(dict(prior_roots=16,new_roots=2,changed_modules=sorted(changed),all_other_selected_object_bytes_identical=True,prior_receipt='NIC_L014',new_receipt='NIC_L022'),indent=1)+'\n')

assert json.loads((E/'NIC_WINDOWS.json').read_text())['checks']
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20*1024*1024,p
assert not list(E.rglob('__pycache__'))
# Every local PASS requires the actual verification marker. Matched controls
# are retained per final configuration; timeouts/undetermined never count.
pairs=[(1,2),(3,4),(5,6),(7,8),(11,12),(13,14),(15,16),(17,18),(19,20),(32,33),(34,35),(36,37),(38,39),(40,41),(46,47),(48,49),(50,51),(52,53),(54,55),(56,57),(58,59),(60,61),(65,66),(67,68),(71,72),(73,74),(77,78),(79,80)]
for positive,negative in pairs:
 p=json.loads((E/f'NIC_K{positive:03d}'/'receipt.json').read_text());n=json.loads((E/f'NIC_K{negative:03d}'/'receipt.json').read_text())
 assert p['exit_status']==0 and n['exit_status']!=0
 assert 'VERIFICATION:- SUCCESSFUL' in (E/f'NIC_K{positive:03d}'/'stdout.log').read_text()
 assert 'VERIFICATION:- FAILED' in (E/f'NIC_K{negative:03d}'/'stdout.log').read_text()
 assert 'timed out' not in (E/f'NIC_K{negative:03d}'/'stdout.log').read_text().lower()
 control=(E/f'NIC_K{negative:03d}'/'stdout.log').read_text();result=control[control.rfind('VERIFICATION RESULT:'):]
 assert 'undetermined' not in result and 'unwinding assertion' not in result
 expected='out[i] != source[i]' if negative==18 else 'NIC Box suffix after allocator abort' if negative==47 else 'NIC later digest after abort' if negative in [33,35,37] else 'NIC forbidden digest'
 assert expected in result
status={
 'opening':('LOCAL-PURITY valid fixed-length input; parent domain association retained',[13,14]),
 'dots':('PARTIAL: main/fold/raw-tail/fold-tail/reduction; stopped decoder and orchestration association OPEN',[48,49,50,51,65,66,67,68,60,61]),
 'trace':('LOCAL-PURITY on canonical E, arbitrary tag/index; deployed non-prover body',[7,8]),
 'geometry':('PARTIAL: arbitrary one-row projection; complete SAME Context/frame installation retained',[11,12]),
 'circle':('OPEN enclosing effect certificate; total SAME-site model domains proved; whole attempts excluded',[28,42,62,77,78]),
 'fields':('PARTIAL: canonical output window and one-word decoder; NIC-D1 stopped-decoder boundary OPEN',[15,16,71,72]),
 'line':('OPEN enclosing effect certificate; total SAME-site model domains proved; whole attempt excluded',[44,75,76,77,78]),
 'product':('LOCAL-PURITY under rule A, exact all-U32 natural product law',[19,20]),
 'double':('LOCAL-PURITY on canonical M31',[3,4]),
 'one':('LOCAL-PURITY constant M31::ONE',[1,2]),
 'subtract':('LOCAL-PURITY on canonical M31 pair',[5,6]),
 'accumulate':('PARTIAL: basis/node/row/flush/tail steps; complete source-to-effect association OPEN',[52,53,54,55,56,57,58,59,79,80])}
closed=dict(status='PARTIAL; target not yet established',row_promotions=[],event_kinds=[dict(kind=k,status=v[0],attempts=[f'NIC_K{i:03d}' for i in v[1]],model_interpretation='NIA_EventInterpretation.eventCode / NIC_PurityFrame.context_frame') for k,v in status.items()],abort_model_roots=['NIC_AbortPrefix.read_fail','NIC_AbortPrefix.read_div','NIC_AbortPrefix.scalar_stopped','NIC_AllocatorPrefix.fail','NIC_AllocatorPrefix.stopped'],abort_prefix_pairs=[[f'NIC_K{i:03d}',f'NIC_K{j:03d}'] for i,j in [(32,33),(34,35),(36,37),(46,47)]],plan_theorems={'DRIVER.events_from_cuts':'PROVED-conditional MODEL instance NIC_DriverPackets.tx1_from_packets; concrete deployed native instance OPEN','EXPERIMENT.same_law':'physical five-field instance OPEN; outside this job'},findings=['NIC-D1: canonical decoder entry precondition stronger than full NFS packet domain; no complete fields/dots credit'],quarantined=[],suspended=[])
(E/'NIC_CLOSED.json').write_text(json.dumps(closed,indent=1)+'\n')
(E/'NIC_LEDGER_DELTA.json').write_text(json.dumps(dict(row_promotions=[],removed_rows=[],changed_native_statuses=[],plan_theorems=closed['plan_theorems'],target_established=False,reason='local purity steps and abort-prefix boundaries do not supply a complete physical TX1 producer'),indent=1)+'\n')
export=json.loads((E/'NIC_EXPORT.json').read_text());cleanup=json.loads((E/'NIC_CLEANUP.json').read_text())
audit=dict(status=closed['status'],headline='AspisR1.RPx_Deployed.deployed',release_source='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',row_promotions=[],kind_counts=dict(Counter(r['kind'] for r in rs)),budget=dict(native_slots=80,native_limit=80,Lean_compiles=sum(r['kind']=='lean' for r in rs),non_Kani_support_scopes=sum(r['kind']!='kani' for r in rs),Lean_limit=60,extraction=0,extraction_limit=0,prelaunch_only=['NIC_L003']),scopes=len(rs),caps=limits,wall_seconds=sum(r['wall_seconds'] for r in rs),peak_rss_kib=max(int(r['peak_rss_kib']) for r in rs),swaps=0,timeout_attempts=[r['attempt'] for r in rs if 'timed out' in (E/r['attempt']/'stdout.log').read_text().lower()],axioms=dict(roots=18,standard_only=True,collect_matches_raw=True,fixtures=8,walker_sha256=json.loads((E/'NIC_WALKER_PIN.json').read_text())['sha256']),scan=dict(attempt='NIC_L023',exit_status=0,modules=len(scan),dangling=0,incompatible_owners=0,import_mismatches=0),cache=dict(seed=json.loads((E/'NIC_SETUP.json').read_text()),export_bytes=export['export_bytes']+json.loads((E/'NIC_STAGE1_EXPORT.json').read_text())['export_bytes'],final_round_export_bytes=export['export_bytes'],retained=export['cache_retained'],closure_sha256=export['closure_sha256'],selected_Aeneas_files=export['selected_Aeneas_files']),removed_own_rebuildable_bytes=cleanup['removed_bytes']+json.loads((E/'NIC_STAGE1_CLEANUP.json').read_text())['removed_bytes'],shipped_files_changed=False,elf_rebuild_triggered=False,source_to_elf_replayed=False,trust_items_added=[],trust_items_removed=[],native_pair_receipt_hashes={f'NIC_K{i:03d}':sha(E/f'NIC_K{i:03d}'/'receipt.json') for pair in pairs for i in pair})
(E/'NIC_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n')
(E/'NIC_VALIDATION.json').write_text(json.dumps(dict(status='PASS: evidence/partial-claim consistency, not target closure',checks=['admissions','caps','offline frozen graphs/locks','final sources','18 raw standard axiom roots (16 unchanged reused, 2 new)','8 fixtures','13648-module scan','native markers and paired controls','cache export','source windows','no promotions','size/hygiene']),indent=1)+'\n')
print(json.dumps({k:audit[k] for k in ['budget','scopes','wall_seconds','peak_rss_kib','timeout_attempts','scan']}))
