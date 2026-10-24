"""Summarize retained receipts only; this script launches no gates."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[3]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-extractor'
prior=E.parent/'rng-transport/ledger.json'
old=json.loads(prior.read_text())
assert old['cumulative_used']==213 and old['kani_used']==44
rows=[]
for p in sorted(E.glob('prover-rw-rng-extractor-build-*/receipt.json')):
    x=json.loads(p.read_text())
    t=x['time_log']
    rows.append(dict(kind='backend-build',attempt=x['build_attempt'],receipt=str(p.relative_to(E)),
        receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),command=x['command'],
        exit=x['exit_status'],wall_seconds=x['wall_seconds'],
        peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t)[1]),
        swaps=int(re.search(r'Swaps: (\d+)',t)[1]),print_axioms=x['print_axioms']))
assert len(rows)==4
for p in sorted(E.glob('extraction-*/receipt.json')):
    x=json.loads(p.read_text())
    rows.append(dict(kind='extraction',attempt=x['attempt'],receipt=str(p.relative_to(E)),
        receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),command=x['target'],
        exit=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],
        swaps=x['swaps'],print_axioms=x['print_axioms']))
assert len(rows)==7
ledger=dict(schema='ProverRwRngExtractor-bounded-ledger-v1',
    prior_ledger_sha256=hashlib.sha256(prior.read_bytes()).hexdigest(),
    lean_new=0,lean_cumulative_used=213,lean_ceiling=220,lean_remaining=7,
    kani_new=0,kani_cumulative_used=44,kani_ceiling=60,kani_remaining=16,
    extraction_used=3,extraction_ceiling=12,extraction_remaining=9,
    backend_build_used=4,backend_build_ceiling=4,backend_build_remaining=0,
    stopped='Backend build ceiling exhausted at compile-time disambiguator error; review required before another build. No build005 or later extraction launched.',
    rows=rows,print_axioms='N/A: no Lean invocation or new checked theorem in this continuation')
(E/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
for p in E.rglob('*.json'):
    assert p.stat().st_size<=5_000_000,(p,p.stat().st_size)
print(json.dumps({k:v for k,v in ledger.items() if k!='rows'}))
