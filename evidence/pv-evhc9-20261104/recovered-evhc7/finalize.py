"""Package evidence and READY only after the single combined scan succeeds."""
from pathlib import Path
import hashlib, json, lzma, shutil, sys, time
E=Path(__file__).resolve().parent
B=E.parent/'codex-pv-evhc6-20261103'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def save(n,v): (E/n).write_text(json.dumps(v,indent=2)+'\n')
blocked='--blocked' in sys.argv
p=read(B/'PLAN.json');scan=None if blocked else read(E/'SCAN.json')
if not blocked: assert scan['dangling_references']==0 and scan['imports_all_match']
receipts=[];bundle={}
for base in [B,E]:
 for f in sorted(base.glob('lean-*/receipt.json')):
  v=read(f);receipts.append((f,v))
  if base==B:bundle[str(f.relative_to(B))]=v
successful=[(f,v) for f,v in receipts if v['exit_status']==0 and v['module'] in p['order']]
assert len(successful)==594 and len({v['module'] for f,v in successful})==594
sources={}
for f,v in successful:
 assert v['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(v['swaps'])==0 and v['wall_seconds']<600 and int(v['peak_rss_kib'])<=7*1024*1024
 for src,h in v['source_hashes'].items():
  snapshot=f.parent/'sources'/src
  assert sha(snapshot)==h
  assert h==p['sources'][v['module']]['sha256']
  sources[src]=dict(sha256=h,text=snapshot.read_text(),source_revision=v['source_revision'])
save('RECEIPT-VALIDATION.json',dict(successful_rebuilds=594,new_rebuilds=2,prior_rebuilds=592,source_snapshots_match=True,normal_caps_match=True,swaps=0,peak_rss_kib=max(int(v['peak_rss_kib']) for f,v in successful),rebuild_wall_seconds=sum(v['wall_seconds'] for f,v in successful),new_rebuild_wall_seconds=sum(v['wall_seconds'] for f,v in successful if f.parent.parent==E),print_axioms_classification='summary-based cached module axiom lists; not raw audits',new_scope_receipts={str(f.relative_to(E)):v for f,v in receipts if f.parent.parent==E}))
inputs=E/'inputs';inputs.mkdir(exist_ok=True)
names=['AUTHORITY.json','BLOCKED.json','PLAN.json','PREFLIGHT.json','AUTHORITY-COPIES.json','SOURCE-GIT-AUDIT.json','NER_STREAM_B_COHORT.jsonl.xz','NER_STREAM_B_COHORT_META.json','NER_REBUILT_OBJECT_PINS.json','NER_SCAN.json','NER_AXIOMS.json','NER_FinalDriverV2.lean','NER_ReferenceTestsV2.lean','RECEIPT-VALIDATION.json','OUTPUT-ENVIRONMENT-CORRECTION.json']
for n in names:
 if (B/n).exists(): shutil.copyfile(B/n,inputs/n)
 else: assert (inputs/n).is_file(),n
shutil.copyfile(B/'sources/PV_BR_FixtureConsumer.lean',inputs/'PV_BR_FixtureConsumer.lean')
for f in sorted(B.glob('admission-*.json')):bundle[f.name]=read(f)
for f in sorted(B.glob('attempt-*.json')):bundle[f.name]=read(f)
for name,value in [('PREDECESSOR-RECEIPTS.json',bundle),('SOURCE-SNAPSHOTS.json',sources)]:
 data=(json.dumps(value,separators=(',',':'))+'\n').encode()
 (E/(name+'.xz')).write_bytes(lzma.compress(data,preset=6))
 (E/(name+'.sha256')).write_text(hashlib.sha256(data).hexdigest()+'\n')
# Recheck all object bytes after the scan, against the pre-scan pins.
manifest=[json.loads(l) for l in (E/'COMBINED-MANIFEST.jsonl').read_text().splitlines()]
for row in manifest:
 for a in row['artifacts']: assert sha(a['path'])==a['sha256'],a['path']
save('POST-SCAN-OBJECT-VALIDATION.json',dict(status='PASS',modules=len(manifest),artifacts=sum(len(r['artifacts']) for r in manifest),manifest_sha256=sha(E/'COMBINED-MANIFEST.jsonl'),all_bytes_unchanged=True))
save('STOP.json',dict(status='BLOCKED_SCAN_MEMORY' if blocked else 'READY_STOP_BEFORE_16GiB',large_admission_requested=False,large_scope_launched=False,consumer_compiled=False,premises_removed=0,privacy_target_established=False))
hashes={str(f.relative_to(E)):sha(f) for f in sorted(E.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name not in ['READY.json','CONTENT-SHA256.json']}
save('CONTENT-SHA256.json',hashes)
ready=dict(status='READY',log='D593',authority=read(B/'AUTHORITY.json'),LEAN_PATH=p['LEAN_PATH'],fresh_namespace_complete_overlay=True,old_incoherent_privacy_objects_reused=0,rebuilt=594,new_rebuild_ids=[92000,92001],scan_id=92050,scan=scan,consumer_source_sha256=p['consumer_sha256'],consumer_source=str(B/'sources/PV_BR_FixtureConsumer.lean'),consumer_body_checked=False,combined_manifest_sha256=sha(E/'COMBINED-MANIFEST.jsonl'),hashes=hashes,content_sha256=sha(E/'CONTENT-SHA256.json'),receipt_validation=read(E/'RECEIPT-VALIDATION.json'),stopped_before_16GiB_admission=True,large_admission_requested=False,large_scope_launched=False,premises_removed=0,privacy_target_established=False)
if blocked:
 failure=read(E/'lean-92050/receipt.json')
 ready.update(status='BLOCKED_SCAN_MEMORY',scan=None,scan_complete=False,dangling_references=None,READY_written=False,scan_failure_receipt='lean-92050/receipt.json',failure_exit_status=failure['exit_status'],failure_wall_seconds=failure['wall_seconds'],failure_peak_rss_kib=failure['peak_rss_kib'],failure_cgroup_memory_peak_bytes=failure['cgroup_memory_peak_bytes'],failure_swaps=failure['swaps'],reason='Lean interpreter excessive memory consumption before any scan rows; first-failure stop; no retry or cap increase',next_deliverable='lead-reviewed changed scan strategy under a separately authorized scope')
 save('BLOCKED.json',ready)
else: save('READY.json',ready)
print(json.dumps(dict(status=ready['status'],rebuilt=594,scan=scan)),flush=True)
