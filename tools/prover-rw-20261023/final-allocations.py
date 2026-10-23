#!/usr/bin/env python3
"""Profile frozen candidate once; reuse the unchanged instrumented v2 receipt."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2];H=R.parent
label=sys.argv[1];binary=H/'native-artifacts'/label;O=H/label
assert not O.exists()
subprocess.run([str(binary),str(O),'0','1'],check=True)
rows=[]
for fixture in ['transfer','withdrawal']:
 a=H/'allocations-baseline-001'/(fixture+'-0');b=O/(fixture+'-0')
 results={k:json.loads((p/'result.json').read_text()) for k,p in [('baseline',a),('candidate',b)]}
 fields={k:results['baseline'].get(k)==results['candidate'].get(k) for k in ['status','callbacks','attempts','audit']}
 files={name:(a/name).read_bytes()==(b/name).read_bytes() for name in ['public.bin','proof.bin']}
 assert all(fields.values()) and all(files.values())
 counts={k:v['allocation_counts_alloc_realloc_requested_bytes'] for k,v in results.items()}
 rows.append(dict(fixture=fixture,counts=counts,delta=[b-a for a,b in zip(counts['baseline'],counts['candidate'])],returned_fields_equal=fields,byte_identity=files))
x=dict(scope='Diagnostic counts for a complete optimized prove call; not timing or peak-memory evidence',baseline_reused='Unchanged v2 instrumented allocations-baseline-001 outputs, coin 0; no unchanged baseline replay',candidate=dict(label=label,sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),bytes=binary.stat().st_size),columns=['allocations','reallocations','cumulative_requested_bytes'],rows=rows)
(H/(label+'-comparison.json')).write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
