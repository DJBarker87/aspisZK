#!/usr/bin/env python3
"""Finalize immutable host receipt metadata; never invokes Lean."""
import hashlib
import json
from pathlib import Path
W=Path(__file__).resolve().parent
E=W/'evidence'
records=[json.loads(l) for l in (E/'modules.jsonl').read_text().splitlines()]
latest={r['module']:r for r in records}
scan=latest.get('RawUnionScan')
if not scan or scan['exit']:
    raise SystemExit('RawUnionScan has not succeeded')
rows=[]
for line in (E/'raw-union.jsonl').read_text().splitlines():
    if line.startswith('RAW_MODULE '):
        m,path,imports=json.loads(line[len('RAW_MODULE '):]);p=Path(path)
        companions=[{'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size} for q in [Path(str(p)+'.server'),Path(str(p)+'.private')] if q.is_file()]
        rows.append({'companions':companions,'module':m,'selected_path':path,'resolved_path':str(p.resolve()),
                     'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'imports':imports})
(E/'raw-object-pins.json').write_text(json.dumps(sorted(rows,key=lambda r:r['module']),indent=2,sort_keys=True)+'\n')
for name in ['plan.json','companion-pins.json']:
    if (W/name).exists():
        (E/name).write_bytes((W/name).read_bytes())
artifacts=[]
for name in ['host-build.py','launch-host.sh','complete-overlay.py','sources/ImportUnionNamedDiscriminant.lean','sources/ImportUnionReleaseGate.lean','sources/RawUnionScan.lean']:
    p=W/name
    artifacts.append({'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size})
(E/'runner-source-pins.json').write_text(json.dumps(artifacts,indent=2)+'\n')
print('pinned union objects',len(rows))
