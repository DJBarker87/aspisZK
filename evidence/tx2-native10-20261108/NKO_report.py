"""Summarize immutable receipts; no proof replay or ledger promotion."""
from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
attempts=[json.loads(x) for x in (E/'NKO_ATTEMPTS.jsonl').read_text().splitlines()]
receipts=[json.loads((E/r['full_receipt']).read_text()) for r in attempts]
expected=json.loads((E/'NKO_AUDIT_ROOTS.json').read_text())['roots'];proofs=[];groups=[]
for p in sorted((E/'NKO_audit').glob('batch*/proof*.json')):
 r=json.loads(p.read_text());assert r['exit_status']==0;proofs+=r['results'];groups.append(dict(path=str(p.relative_to(E)),**{k:r[k] for k in ['target','exit_status','wall_seconds','peak_rss_kib','swaps']}))
assert len(proofs)==len(expected) and {r['root'] for r in proofs}==set(expected)
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in proofs)
scan=json.loads((E/'NKO_audit/scan/scan.json').read_text());assert scan['exit_status']==0 and 'NFN_SCAN_ZERO_DANGLING' in (E/'NKO_audit/scan/scan.log').read_text()
combined=next(r for r in receipts if r['kind']=='lean' and r['module']=='NKO_COMBINED_IMPORT');assert combined['exit_status']==0
assert all(r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'} for r in receipts)
summary=lambda r:{k:r[k] for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']}
report=dict(status='PASS',scope='Combined import, raw ax2 and NFX coherence audit; NOT a native parent certificate',target='TX2:065',target_established=False,composed_new_closed_rows=0,combined_audit_campaigns=1,combined_import=summary(combined),headline='AspisR1.RPx_Deployed.deployed',selected_modules=len(json.loads((E/'NKO_MODULES.json').read_text())),raw_roots=len(proofs),all_raw_equal=True,raw_axioms=sorted({a for r in proofs for a in r['walked_axioms']}),raw_groups=groups,NFX_scan={k:scan[k] for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']},loaded_modules=sum(1 for l in (E/'NKO_LOADED_scan.jsonl').read_text().splitlines() if l.strip()),native_pairs=len(json.loads((E/'NKO_NATIVE_PAIRS.json').read_text())['pairs']),fidelity_checks=len(json.loads((E/'NKO_CONTRACT_CONTROLS.json').read_text())['controls']),budget=dict(Kani_used=sum(r['kind']=='kani' for r in receipts),Kani_max=60,formal_support_used=sum(r['kind']!='kani' for r in receipts),formal_support_max=120,extraction_used=0),budget_stop_reason='NKO_REMAINING.md member-by-member audit: no independent Lean-only member remains; complete native parent G and two externally owned CLOSED children unavailable',trust_added=[],trust_transport='P6/D188 option A reclassification; no removal',remaining_children=['C01/TX2:124','C04/TX2:053'],parent_native_G='OPEN',all_receipts='NKO_ATTEMPTS.jsonl',release_source_changed=False,full_frozen_manifest_replayed=False,keys_touched=False,shipped_files_changed=False)
for n in ['NKO_SOURCE_VERIFICATION.json','NKO_EXPORT.json','NKO_EXPORT_VERIFY.json','NKO_RETENTION.json']:
 if (E/n).is_file():report[n[:-5]]=json.loads((E/n).read_text()) if n!='NKO_EXPORT.json' else {k:v for k,v in json.loads((E/n).read_text()).items() if k!='files'}
(E/'NKO_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
(E/'NKO_RECEIPT_INDEX.json').write_text(json.dumps([summary(r) for r in receipts],indent=2)+'\n')
print(json.dumps(dict(audit='PASS',raw_roots=len(proofs),modules=report['selected_modules'],budget=report['budget'],target_established=False)))
