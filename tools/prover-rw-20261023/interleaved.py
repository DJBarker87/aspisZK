#!/usr/bin/env python3
"""Sequential, alternating v2/candidate pairs; relative implementation gate only."""
from pathlib import Path
import hashlib,json,os,statistics,subprocess,sys,time
H=Path(__file__).resolve().parents[3]
label=sys.argv[1]
O=H/('interleaved-'+label);O.mkdir()
binaries={'baseline':H/'native-artifacts/baseline','candidate':H/'native-artifacts'/label}
rows=[]
for sample in range(5):
    order=['baseline','candidate'] if sample%2==0 else ['candidate','baseline']
    for name in order:
        out=O/f'{name}-{sample}'
        start={'utc':time.time(),'loadavg':Path('/proc/loadavg').read_text().strip()}
        subprocess.run([str(binaries[name]),str(out),str(100+sample),'1'],check=True,stdout=subprocess.DEVNULL)
        rows.append(dict(sample=sample,kind=name,**start))
comparisons=[];timing=[]
for fixture in ['transfer','withdrawal']:
    times={'baseline':[],'candidate':[]}
    for sample in range(5):
        paths={k:O/f'{k}-{sample}'/f'{fixture}-{100+sample}' for k in binaries}
        results={k:json.loads((p/'result.json').read_text()) for k,p in paths.items()}
        equal={k:results['baseline'].get(k)==results['candidate'].get(k) for k in ['status','callbacks','attempts','audit']}
        files={}
        for file in ['public.bin','proof.bin']:
            a=(paths['baseline']/file).read_bytes();b=(paths['candidate']/file).read_bytes()
            files[file]=dict(byte_identical=a==b,bytes=len(a),sha256=hashlib.sha256(a).hexdigest())
        comparisons.append(dict(fixture=fixture,sample=sample,returned_fields_equal=equal,files=files,results=results))
        for k in times:times[k].append(results[k]['seconds'])
    med={k:statistics.median(v) for k,v in times.items()}
    timing.append(dict(fixture=fixture,seconds=times,median_seconds=med,ratio=med['candidate']/med['baseline'],within_10_percent=med['candidate']<=1.1*med['baseline']))
passed=all(all(x['returned_fields_equal'].values()) and all(v['byte_identical'] for v in x['files'].values()) for x in comparisons) and all(t['within_10_percent'] for t in timing)
result=dict(label=label,gate='Relative only per lead continuation; absolute quiet-host gate pending',passed=passed,workers=16,rows=rows,timing=timing,comparisons=comparisons,binaries={k:dict(sha256=hashlib.sha256(v.read_bytes()).hexdigest(),bytes=v.stat().st_size) for k,v in binaries.items()})
(O/'comparison.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['label','gate','passed','workers','timing']},indent=2))
raise SystemExit(0 if passed else 3)
