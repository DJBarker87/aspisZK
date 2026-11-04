"""Freeze the exact ID-limit stop; never imply the missing scan passed."""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(n,v):(E/n).write_text(json.dumps(v,indent=2)+'\n')
p=json.load(open(E/'PLAN.json'));receipts=[]
for f in sorted(E.glob('lean-*/receipt.json')):
 r=json.load(open(f));assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert str(r['swaps'])=='0'
 for n,h in r['source_hashes'].items():assert sha(f.parent/'sources'/n)==h
 assert r['exit_status']==0 or r['attempt']=='lean-91400'
 receipts.append(dict(attempt=r['attempt'],module=r['module'],exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r['source_revision'],print_axioms=r['print_axioms'],receipt=str(f.relative_to(E)),sha256=sha(f)))
success={r['module'] for r in receipts if r['exit_status']==0 and r['module'] in p['sources']};pending=[m for m in p['order'] if m not in success]
assert len(success)==592 and pending==['PV_BR_PV_EVH_Residual','PV_BR_PV_EVH_Deployed'],pending
assert not (E/'READY.json').exists()
save('RECEIPT-SUMMARY.json',receipts)
save('PENDING-REBUILDS.json',dict(authorized=False,additional_unused_ids_needed=2,LEAN_PATH=p['LEAN_PATH'],scopes=[dict(module=m,source='sources/'+m.replace('.','/')+'.lean',source_sha256=p['sources'][m]['sha256'],source_revision=p['sources'][m]['revision'],command=[p['sysroot']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','objects/'+m.replace('.','/')+'.olean','sources/'+m.replace('.','/')+'.lean'],caps=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),mechanical_reconciliation=True,charged_proof_attempt=False) for m in pending]))
refused=[int(f.stem.split('-')[1]) for f in E.glob('admission-*.json') if json.load(open(f)).get('allowed') is False]
validation=dict(successful_rebuilds=len(success),scanner_helper_check='lean-91390/receipt.json',source_snapshots_match=True,normal_caps_match=True,swaps=0,peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),rebuild_wall_seconds=sum(r['wall_seconds'] for r in receipts if r['module'] in p['sources']),refused_ids=sorted(refused),output_environment_failure_id=91400,attempts_in_authorized_rebuild_range=len(list(E.glob('attempt-91[4-9][0-9][0-9].json'))))
assert validation['attempts_in_authorized_rebuild_range']==600 and len(refused)==7
save('RECEIPT-VALIDATION.json',validation)
content={str(f.relative_to(E)):sha(f) for f in sorted(E.rglob('*')) if f.is_file() and '__pycache__' not in f.parts and f.name not in ['CONTENT-SHA256.json','BLOCKED.json']}
save('CONTENT-SHA256.json',content)
save('BLOCKED.json',dict(status='BLOCKED_ON_ADDITIONAL_REBUILD_IDS',authority='coherent NER Stream B cohort; h6 double-prime authority',research_revision=json.load(open(E/'AUTHORITY.json'))['research_revision'],fresh_namespace_complete_overlay=True,old_privacy_objects_reused=0,successful_rebuilds=len(success),required_rebuilds=594,pending_modules=pending,scanner_helper_compiled=True,combined_scan_run=False,READY_written=False,large_admission_requested=False,large_scope_launched=False,stopped_before_16GiB=True,additional_unused_rebuild_ids_needed=2,additional_allocation_authorized=False,original_range_exhausted=[91400,91999],receipt_validation=validation,hashes={n:sha(E/n) for n in ['AUTHORITY.json','NER_STREAM_B_COHORT.jsonl.xz','NER_STREAM_B_COHORT_META.json','NER_REBUILT_OBJECT_PINS.json','PLAN.json','AUTHORITY-COPIES.json','SOURCE-GIT-AUDIT.json','RECEIPT-SUMMARY.json','RECEIPT-VALIDATION.json','PENDING-REBUILDS.json','PV_NER_Scan.lean','CONTENT-SHA256.json']}))
print(json.dumps(validation,indent=2));print('PENDING',pending)
