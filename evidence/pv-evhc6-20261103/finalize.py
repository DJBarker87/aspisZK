"""Validate receipts and zero-dangling scan, pin all artifacts, then STOP."""
from pathlib import Path
import json,hashlib,lzma
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,v):(B/n).write_text(json.dumps(v,indent=2)+'\n')
p=json.load(open(B/'PLAN.json'));scan=json.load(open(B/'SCAN.json'));assert scan['status']=='coherent' and scan['dangling_references']==0
receipts=[]
for f in sorted(B.glob('lean-*/receipt.json')):
 r=json.load(open(f));assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 for n,h in r['source_hashes'].items():assert sha(f.parent/'sources'/n)==h
 if r['attempt']!='lean-91400':assert r['exit_status']==0,r['attempt']
 receipts.append(dict(attempt=r['attempt'],module=r['module'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],print_axioms=r['print_axioms'],receipt=str(f.relative_to(B)),sha256=sha(f)))
success={r['module'] for r in receipts if r['exit_status']==0};assert set(p['order'])<=success
manifest=[json.loads(l) for l in (B/'COMBINED-MANIFEST.jsonl').read_text().splitlines()]
for r in manifest:
 for v in r['artifacts']:assert sha(v['path'])==v['sha256']
# No compiler/runtime output left unpinned. Objects have their own complete manifest.
content={str(f.relative_to(B)):sha(f) for f in sorted(B.rglob('*')) if f.is_file() and not f.is_relative_to(B/'objects') and f.name not in ['READY.json','CONTENT-SHA256.json','build-resumed.log','build.log']}
save('CONTENT-SHA256.json',content)
save('RECEIPT-SUMMARY.json',receipts)
save('READY.json',dict(status='READY_FOR_LEAD_SCOPE_REVIEW',task='D578 coherent NER authority and fresh privacy overlay',authority=json.load(open(B/'AUTHORITY.json')),fresh_overlay=True,old_privacy_objects_reused=0,rebuild_count=len(p['order']),successful_rebuild_ids=[int(r['attempt'][5:]) for r in receipts if r['module'] in p['sources'] and r['exit_status']==0],environment_failure='OUTPUT-ENVIRONMENT-CORRECTION.json',scan=scan,LEAN_PATH=p['LEAN_PATH'],consumer_source_sha256=p['consumer_sha256'],consumer_source='sources/PV_BR_FixtureConsumer.lean',consumer_body_elaborated=False,normal_caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),large_admission_requested=False,large_scope_launched=False,stopped_before_16GiB=True,next_action='Lead asks Stream A for scope; full PV_BR_FixtureConsumer body remains lead-only.',hashes={n:sha(B/n) for n in ['NER_STREAM_B_COHORT.jsonl.xz','NER_STREAM_B_COHORT_META.json','NER_REBUILT_OBJECT_PINS.json','PLAN.json','PREFLIGHT.json','AUTHORITY-COPIES.json','COMBINED-MANIFEST.jsonl','COMBINED-SCAN-ROWS.jsonl','SCAN.json','PV_NER_Scan.lean','RECEIPT-SUMMARY.json','CONTENT-SHA256.json']},all_evidence_hashes=content))
print('READY: STOP BEFORE ANY 16 GiB ADMISSION')
