#!/usr/bin/env python3
"""Final candidate-only absolute gate, after an explicit quiet-host check."""
from pathlib import Path
import hashlib,json,statistics,subprocess,sys,time
R=Path(__file__).resolve().parents[2];H=R.parent
label=sys.argv[1];O=H/('absolute-'+label);O.mkdir(exist_ok=False)
binary=H/'native-artifacts'/label;rows=[]
for sample in range(5):
    # Refuse before timing if any other capped user job is populated.
    subprocess.run(['python3',str(R/'tools/prover-rw-20261023/quiet-preflight.py'),str(O/f'quiet-before-{sample}.json')],check=True,stdout=subprocess.DEVNULL)
    subprocess.run([str(binary),str(O/f'sample-{sample}'),str(100+sample),'1'],check=True,stdout=subprocess.DEVNULL)
    subprocess.run(['python3',str(R/'tools/prover-rw-20261023/quiet-preflight.py'),str(O/f'quiet-after-{sample}.json')],check=True,stdout=subprocess.DEVNULL)
    rows.append(dict(sample=sample,utc=time.time()))
timing=[]
for fixture in ['transfer','withdrawal']:
    results=[json.loads((O/f'sample-{sample}'/f'{fixture}-{100+sample}'/'result.json').read_text()) for sample in range(5)]
    assert all(r['status']=='Ok' for r in results),results
    times=[r['seconds'] for r in results];median=statistics.median(times)
    timing.append(dict(fixture=fixture,seconds=times,median_seconds=median,under_15_seconds=median<15))
x=dict(gate='Final quiet-host absolute gate',workers=16,rows=rows,timing=timing,passed=all(t['under_15_seconds'] for t in timing),binary=dict(path=str(binary),sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),bytes=binary.stat().st_size))
(O/'comparison.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
raise SystemExit(0 if x['passed'] else 1)
