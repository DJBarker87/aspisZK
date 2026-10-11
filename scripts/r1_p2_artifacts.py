#!/usr/bin/env python3
"""UNPROVED P2: build-host artifact inventory; never copy artifact contents."""
import hashlib,json,os
from pathlib import Path
root=Path(__file__).resolve().parent.parent
out=root/'results/r1-precheck-20261010'
records=[]
for p in sorted(out.rglob('*')):
    if not p.is_file() or p.name.endswith('-keypair.json') or p.name=='litesvm-payer.json':
        continue
    if p.suffix not in ['.so','.text','.txt','.bin'] and not ('bin' in p.relative_to(out).parts and os.access(p,os.X_OK)):
        continue
    records.append({'path':str(p),'size_bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'retained_on_build_host':True})
record={'label':'UNPROVED R1 COST PROBE P2','build_host':os.uname().nodename,'artifacts':records,
    'private_keys':'Generated program and LiteSVM keys retained in place, excluded from evidence copying and this content inventory.',
    'retention_gap':{'artifact':'initial S1 native-gate executable','status':'overwritten in the private Cargo cache before archival','available_evidence':'native acceptance/trace/rejection JSON, capped build/run logs and exact source manifest; S1 proof/public bytes and both SBF artifacts are retained','unchanged_measurement_rerun':False}}
(out/'build-host-artifacts.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'artifact_count':len(records),'total_artifact_bytes':sum(x['size_bytes'] for x in records),'retention_gap':record['retention_gap']}))
