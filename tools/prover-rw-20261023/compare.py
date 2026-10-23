#!/usr/bin/env python3
"""Compare retained full bytes on host; export only metadata, never proofs/keys."""
from pathlib import Path
import hashlib,json,statistics,sys
h=Path(sys.argv[1])
rows=[]
for name in ['transfer','withdrawal']:
    for coin in range(5):
        a=h/'fixtures-baseline'/f'{name}-{coin}'
        b=h/'fixtures-opening'/f'{name}-{coin}'
        ar=json.loads((a/'result.json').read_text())
        br=json.loads((b/'result.json').read_text())
        equal={k:ar.get(k)==br.get(k) for k in ['status','callbacks','attempts','audit']}
        files={}
        for n in ['public.bin','proof.bin']:
            ap,bp=a/n,b/n
            files[n]={'baseline_exists':ap.exists(),'candidate_exists':bp.exists()}
            if ap.exists() and bp.exists():
                ab,bb=ap.read_bytes(),bp.read_bytes()
                files[n].update(byte_identical=ab==bb,bytes=len(ab),sha256=hashlib.sha256(ab).hexdigest())
        rows.append(dict(fixture=name,coin=coin,baseline=ar,candidate=br,
            returned_fields_equal=equal,files=files))
timing=[]
for name in ['transfer','withdrawal']:
    rs=[r for r in rows if r['fixture']==name]
    baseline=statistics.median(r['baseline']['seconds'] for r in rs)
    candidate=statistics.median(r['candidate']['seconds'] for r in rs)
    timing.append(dict(fixture=name,samples=5,workers=16,baseline_median_seconds=baseline,
        candidate_median_seconds=candidate,ratio=candidate/baseline,
        under_15_seconds=candidate<15,within_10_percent=candidate<=baseline*1.1))
pair_ok=all(all(r['returned_fields_equal'].values()) and all(f.get('byte_identical',False) for f in r['files'].values()) for r in rows)
speed_ok=all(t['under_15_seconds'] and t['within_10_percent'] for t in timing)
x=dict(scope='Intermediate owned retry/opening candidate; not completed Stage 2',
    paired_runs=10,required_differential_runs=1000,differential_gate_complete=False,
    successful_fixture_byte_and_status_comparisons_pass=pair_ok,timing=timing,
    timing_gate_pass=speed_ok,decision='STOP: performance gate failed' if not speed_ok else 'Continue implementation; adoption gates remain open',
    leaves='Unchanged CT arithmetic bodies; no new Kani gate run',
    l1='Record equality not yet gated',print_axioms='N/A: native differential and fixture timings',comparisons=rows)
(h/'opening-comparison.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:x[k] for k in ['scope','paired_runs','successful_fixture_byte_and_status_comparisons_pass','timing','timing_gate_pass','decision']},indent=2))
if not pair_ok:sys.exit(2)
if not speed_ok:sys.exit(3)
