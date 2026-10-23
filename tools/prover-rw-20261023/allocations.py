#!/usr/bin/env python3
"""Diagnostic allocator counts; never use these instrumented durations as timings."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];H=R.parent
for kind in ['baseline','candidate']:
    subprocess.run([str(H/'native-artifacts'/('allocations-'+kind+'-001')),str(H/('allocations-'+kind+'-001')),'0','1'],check=True)
rows=[]
for fixture in ['transfer','withdrawal']:
    D={k:H/('allocations-'+k+'-001')/(fixture+'-0') for k in ['baseline','candidate']}
    r={k:json.loads((p/'result.json').read_text()) for k,p in D.items()}
    c={k:v['allocation_counts_alloc_realloc_requested_bytes'] for k,v in r.items()}
    proof={f:(D['baseline']/f).read_bytes()==(D['candidate']/f).read_bytes() for f in ['public.bin','proof.bin']}
    assert all(proof.values())
    rows.append(dict(fixture=fixture,baseline=c['baseline'],candidate=c['candidate'],delta=[b-a for a,b in zip(c['baseline'],c['candidate'])],columns=['allocations','reallocations','cumulative_requested_bytes'],full_byte_identity=proof))
result=dict(scope='Instrumentation-only total counts during full prove call; not peak memory and not timing evidence',candidate='Owned pipeline before prepare_opening helper split; same allocation operations',rows=rows)
(H/'allocation-comparison.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
