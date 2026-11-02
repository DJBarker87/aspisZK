"""Summarize committed focused-run receipts; never runs a compiler or audit walker."""
from pathlib import Path
import hashlib,json,subprocess
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
allrows=sorted([json.loads(p.read_text()) for p in E.glob('receipt-*.json')],key=lambda r:r['attempt'])
rows=[r for r in allrows if r['attempt']>=90228]
assert rows and [r['attempt'] for r in rows]==list(range(90228,90228+len(rows)))
assert all(r['attempt']<90297 for r in rows)
mode='SUMMARY-BASED cached per-module axiom lists (ax1/ax1-prime)'
inherited=json.loads((E/'axioms-classification-D569.json').read_text())
out=dict(base='e08d80635057554f109651811ea8be512e24b1ff',mode=mode,raw_walk=False,full_data_coherence=False,
    NEP_driver_source=inherited['NEP_driver_source'],
    receipts=[dict(attempt=r['attempt'],accepted=r['accepted'],
      receipt_sha256=sha((E/f"receipt-{r['attempt']}.json").read_bytes()),
      axioms=r['axioms'],credit='accepted focused compile' if r['accepted'] else 'FAILED; no proof credit') for r in rows])
(E/'axioms-classification-D572.json').write_text(json.dumps(out,indent=2)+'\n')
resume=[r for r in allrows if r['attempt']>=79565]
accepted=[r for r in rows if r['accepted']]
summary=dict(base='e08d80635057554f109651811ea8be512e24b1ff',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
    new_attempts=len(rows),new_accepted=len(accepted),new_failed=len(rows)-len(accepted),
    resume_attempts=len(resume),resume_accepted=sum(r['accepted'] for r in resume),
    resume_failed=sum(not r['accepted'] for r in resume),remaining=100-len(resume),
    next_fresh=90228+len(rows),cumulative_attempts=len(allrows),
    cumulative_accepted=sum(r['accepted'] for r in allrows),
    cumulative_failed=sum(not r['accepted'] for r in allrows),
    peak_rss_kbytes=max(int(r['peak_rss_kbytes']) for r in rows),
    walls={str(r['attempt']):r['wall'] for r in rows},
    swap=sum(int(r['swaps']) for r in rows),
    axioms_mode=mode,raw_walk=False,full_data_coherence=False,
    audit_ids_untouched=[79397,79398,79399,79597,79598,79599,90297,90298,90299],
    rows_removed=[],trust_fields_added=[],native_runs=0,kani_runs=0,release_replay=False)
(E/'summary-D572.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'commits-D572.txt').write_text(subprocess.check_output(['git','log','--oneline','e08d806350..HEAD'],text=True))
print(json.dumps({k:summary[k] for k in ['new_attempts','new_accepted','new_failed','remaining','next_fresh','peak_rss_kbytes','swap']}))
