#!/usr/bin/env python3
"""Classify raw CBMC properties without hiding exit10 or the scan abstraction.
Only traces are omitted from the source-only projection; every property/status,
source location, property class and description is preserved. Raw log is pinned.
"""
from pathlib import Path
import hashlib,json,sys
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/sys.argv[1]
p=O/'step2.log';raw=p.read_bytes();rows=json.loads(raw);props=[prop for row in rows for prop in row.get('result',[])]
assert props,'No CBMC properties found'
projection=[]
for prop in props:
 projection.append({k:v for k,v in prop.items() if k!='trace'})
noncover=[p for p in projection if p.get('sourceLocation',{}).get('propertyClass')!='cover']
covers=[p for p in projection if p.get('sourceLocation',{}).get('propertyClass')=='cover']
assert len(noncover)+len(covers)==len(props)
summary=dict(schema='focused-extractor-proof-packet-v1',raw_log_sha256=hashlib.sha256(raw).hexdigest(),raw_log_bytes=len(raw),raw_exit=json.loads((O/'cbmc-exit.json').read_text()),property_count=len(props),noncover_count=len(noncover),all_noncover_properties_passed=all(p['status']=='SUCCESS' for p in noncover),covers_satisfied=sum(p['status']=='FAILURE' for p in covers),covers_total=len(covers),qualification='Parent context with explicitly abstracted pure scan. Raw exit is unchanged. CBMC cover FAILURE denotes an attainable cover condition, NOT a failed ordinary assertion. All properties retained; trace payload omitted from projection. This does not establish concrete SDK-to-owned source correspondence.',properties=projection)
(O/'properties-without-traces.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['properties','qualification','raw_exit']}))
