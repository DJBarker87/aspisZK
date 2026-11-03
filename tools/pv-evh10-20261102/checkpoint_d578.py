"""D578 receipt accounting; not a compiler, manifest replay or raw axiom audit."""
from pathlib import Path
import hashlib,json,subprocess
E=Path('evidence/pv-evh10-20261102');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=sorted([json.loads(p.read_text()) for p in E.glob('receipt-*.json')],key=lambda r:r['attempt'])
new=[r for r in rows if r['attempt']>=90248];resume=[r for r in rows if r['attempt']>=79565]
assert [r['attempt'] for r in new]==list(range(90248,90248+len(new)))
base='034dfee6ac'
summary=dict(base=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 session_attempts=len(new),session_accepted=sum(r['accepted'] for r in new),session_failed=sum(not r['accepted'] for r in new),
 resume_attempts=len(resume),remaining=100-len(resume),next_fresh=90248+len(new),
 cumulative_attempts=len(rows),cumulative_accepted=sum(r['accepted'] for r in rows),cumulative_failed=sum(not r['accepted'] for r in rows),
 peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in new),swaps=sum(int(r['swaps']) for r in new),
 targets=[dict(attempt=r['attempt'],target=r['target'],accepted=r['accepted'],exit=r['exit'],wall=r['wall'],peak_rss_kbytes=r['peak_rss_kbytes'],swaps=r['swaps'],revision=r['source_revision'],axioms=r['axioms'],receipt_sha256=sha(E/f"receipt-{r['attempt']}.json")) for r in new],
 axioms_mode='SUMMARY-BASED cached module lists (ax1-prime); no full-data NEP/coherence claim',
 audit_ids_untouched=[79397,79398,79399,79597,79598,79599,90297,90298,90299],
 rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0,release_replay=False,
 compile_guard_sha256=sha(Path('tools/pv-evh10-20261102/compile.py')))
(E/'summary-D578.json').write_text(json.dumps(summary,indent=2)+'\n')
axioms=json.loads((E/'axioms-classification-session2.json').read_text())
(E/'axioms-classification-D578.json').write_text(json.dumps(dict(mode=summary['axioms_mode'],raw_walk=False,full_data_coherence=False,
 NEP_driver_source=axioms['NEP_driver_source'],receipts=[dict(attempt=r['attempt'],axioms=r['axioms'],credit='focused compile only' if r['accepted'] else 'FAILED; no proof credit') for r in new]),indent=2)+'\n')
(E/'commits-D578.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],text=True))
print(json.dumps({k:summary[k] for k in ['session_attempts','session_accepted','session_failed','remaining','next_fresh','peak_rss_kbytes','swaps']}))
