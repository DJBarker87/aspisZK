"""Receipt accounting only. Not a compiler, replay, or raw axioms walker."""
from pathlib import Path
import hashlib,json,subprocess
E=Path('evidence/pv-evh10-20261102');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allrows=sorted([json.loads(p.read_text()) for p in E.glob('receipt-*.json')],key=lambda r:r['attempt'])
rows=[r for r in allrows if r['attempt']>=90237]
assert [r['attempt'] for r in rows]==list(range(90237,90237+len(rows)))
resume=[r for r in allrows if r['attempt']>=79565]
mode='SUMMARY-BASED cached module axiom lists (ax1-prime); full-data NEP/coherence not established'
base='a5e973e378829b2b74f294f4d7549a17b5a7faa7'
summary=dict(base=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 session_attempts=len(rows),session_accepted=sum(r['accepted'] for r in rows),session_failed=sum(not r['accepted'] for r in rows),
 resume_attempts=len(resume),remaining=100-len(resume),next_fresh=90237+len(rows),cumulative_attempts=len(allrows),
 cumulative_accepted=sum(r['accepted'] for r in allrows),cumulative_failed=sum(not r['accepted'] for r in allrows),
 peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in rows),swap=sum(int(r['swaps']) for r in rows),
 targets=[dict(attempt=r['attempt'],target=r['target'],accepted=r['accepted'],exit=r['exit'],wall=r['wall'],peak_rss_kbytes=r['peak_rss_kbytes'],swaps=r['swaps'],revision=r['source_revision'],axioms=r['axioms'],receipt_sha256=sha(E/f"receipt-{r['attempt']}.json")) for r in rows],
 axioms_mode=mode,raw_walk=False,full_data_coherence=False,
 audit_ids_untouched=[79397,79398,79399,79597,79598,79599,90297,90298,90299],
 rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0,release_replay=False,
 compile_guard_sha256=sha(Path('tools/pv-evh10-20261102/compile.py')))
(E/'summary-session2.json').write_text(json.dumps(summary,indent=2)+'\n')
inherited=json.loads((E/'axioms-classification-D572.json').read_text())
(E/'axioms-classification-session2.json').write_text(json.dumps(dict(mode=mode,raw_walk=False,full_data_coherence=False,
 NEP_driver_source=inherited['NEP_driver_source'],receipts=[dict(attempt=r['attempt'],axioms=r['axioms'],credit='focused compile only' if r['accepted'] else 'FAILED: no proof credit') for r in rows]),indent=2)+'\n')
(E/'commits-session2.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],text=True))
print(json.dumps({k:summary[k] for k in ['session_attempts','session_accepted','session_failed','remaining','next_fresh','peak_rss_kbytes','swap']}))
