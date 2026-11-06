"""Index exact receipts and completed component gates, never promote ledger rows."""
from pathlib import Path
import json,hashlib
from NJU_read import read_text
E=Path(__file__).resolve().parent
receipts=sorted((json.loads(p.read_text()) for p in E.glob('NJU_[LK]*/receipt.json')),key=lambda r:r['attempt'])
K=[r for r in receipts if r['kind']=='kani'];L=[r for r in receipts if r['attempt'].startswith('NJU_L')]
assert len(K)<=80 and len(L)<=100
rows=[]
for r in receipts:
 rows.append({k:r[k] for k in ['attempt','kind','module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','limits','cgroup','source_hashes','print_axioms']})
(E/'NJU_RESOURCE_SUMMARY.json').write_text(json.dumps(rows,indent=1)+'\n')
get=lambda a:next(r for r in receipts if r['attempt']==a)
assert all(get(a)['exit_status']==0 for a in ['NJU_L092','NJU_L097','NJU_L098','NJU_L099','NJU_L100'])
raw=[]
for p in sorted((E/'NJU_audit/all').glob('proof*.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0
 raw+=r['results']
roots=json.loads((E/'NJU_AUDIT_ROOTS.json').read_text())['roots'];assert set(roots)=={r['root'] for r in raw}
assert all(r['equal'] and set(r['walked_axioms'])<={'Classical.choice','Quot.sound','propext'} for r in raw)
scan=json.loads((E/'NJU_audit/scan/scan.json').read_text());assert scan['exit_status']==0
scanlog=read_text(E/'NJU_audit/scan/scan.log');assert 'NFN_SCAN_ZERO_DANGLING' in scanlog
selected=json.loads((E/'NJU_SELECTED_SOURCES.json').read_text())
for m,r in selected.items():assert hashlib.sha256((E/(m+'.lean')).read_bytes()).hexdigest()==r['sha256']
report=dict(schema_version=1,status='PASS_COMPONENT_AUDIT_PARENT_OPEN',headline='AspisR1.RPx_Deployed.deployed',target='TX2:065',security_target_established=False,new_closed_rows=0,full_combined_audits=1,budget={'used':{'K':len(K),'L':len(L),'E':0},'limits':{'K':80,'L':100,'E':0},'unused_native_disposition':'NJU_REMAINING.md M01-M13, self-owned Lean native association and absent CLOSED Merkle children'},selected_modules=len(selected),raw_roots=len(raw),raw_results=raw,raw_axioms=sorted({a for r in raw for a in r['walked_axioms']}),scan={'exit_status':scan['exit_status'],'wall_seconds':scan['wall_seconds'],'peak_rss_kib':scan['peak_rss_kib'],'swaps':scan['swaps'],'result_lines':[x for x in scanlog.splitlines() if 'NFN_' in x]},combined_import_receipt='NJU_L092/receipt.json',raw_receipt='NJU_L097/receipt.json',scan_receipt='NJU_L098/receipt.json',export_receipt='NJU_L099/receipt.json',retained_export_verify_receipt='NJU_L100/receipt.json',fixture_reuse={'receipt':'evidence/tx2-native7-20261108/NJR_L051/receipt.json','method':'same unchanged raw ax2/NFX implementation; only root/import selectors differ; NJU_PROOF_DRIVER.diff, NJU_SCAN_DRIVER.diff, NJU_WALKER_PIN.json','fresh_fixture_run':False},new_trust_rows=[],transport='P6/D188 option-A reclassification, never removal',whole_manifest_replayed=False,shipped_files_changed=False)
(E/'NJU_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n')
(E/'NJU_RAW_RESULTS.json').write_text(json.dumps(raw,indent=1)+'\n')
print(json.dumps({'K':len(K),'L':len(L),'raw_roots':len(raw),'scan_exit':0,'target':'OPEN'}))
