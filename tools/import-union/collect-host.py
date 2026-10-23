#!/usr/bin/env python3
"""Finalize immutable host receipt metadata; never invokes Lean."""
import hashlib
import json
from pathlib import Path
W=Path(__file__).resolve().parent
E=W/'evidence'
hashes={}
def digest(p):
    resolved=p.resolve()
    before=resolved.stat()
    signature=(before.st_ino,before.st_size,before.st_mtime_ns)
    key=(str(resolved),signature)
    if key not in hashes:
        h=hashlib.sha256()
        with resolved.open('rb') as f:
            for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
        after=resolved.stat()
        assert (after.st_ino,after.st_size,after.st_mtime_ns)==signature, ('concurrent artifact change',str(p))
        hashes[key]=h.hexdigest()
    return hashes[key]
records=[json.loads(l) for l in (E/'modules.jsonl').read_text().splitlines()]
latest={r['module']:r for r in records}
scan=latest.get('RawUnionScan')
if not scan or scan['exit']:
    raise SystemExit('RawUnionScan has not succeeded')
rows=[]
for line in (E/'raw-union.jsonl').read_text().splitlines():
    if line.startswith('RAW_MODULE '):
        m,path,imports=json.loads(line[len('RAW_MODULE '):]);p=Path(path)
        companions=[{'path':str(q),'sha256':digest(q),'bytes':q.stat().st_size} for q in [Path(str(p)+'.server'),Path(str(p)+'.private')] if q.is_file()]
        rows.append({'companions':companions,'module':m,'selected_path':path,'resolved_path':str(p.resolve()),
                     'sha256':digest(p),'bytes':p.stat().st_size,'imports':imports})
(E/'raw-object-pins.json').write_text(json.dumps(sorted(rows,key=lambda r:r['module']),indent=2,sort_keys=True)+'\n')
for name in ['plan.json','companion-pins.json']:
    if (W/name).exists():
        (E/name).write_bytes((W/name).read_bytes())
plan=json.loads((W/'plan.json').read_text())
paths=[W/'objects']+[Path(p) for p in plan['lean_paths']]
checks=[]
for rec in plan['ordered']:
    r=latest[rec['module']]
    assert r['exit']==0, ('unfinished target',rec['module'])
    obj=W/'objects'/(rec['module'].replace('.','/')+'.olean')
    assert digest(obj)==r['object_sha256'], ('output drift',rec['module'])
    for dep,old_path,expected in r['deps']:
        selected=next(p/(dep.replace('.','/')+'.olean') for p in paths if (p/(dep.replace('.','/')+'.olean')).is_file())
        actual=digest(selected)
        assert actual==expected, ('dependency drift',rec['module'],dep,old_path,str(selected))
        checks.append({'consumer':rec['module'],'dependency':dep,'selected_path':str(selected),'sha256':actual})
(E/'final-dependency-check.json').write_text(json.dumps(checks,indent=2,sort_keys=True)+'\n')
artifacts=[]
for name in ['host-build.py','launch-host.sh','complete-overlay.py','collect-host.py','sources/ImportUnionNamedDiscriminant.lean','sources/ImportUnionReleaseGate.lean','sources/RawUnionScan.lean']:
    p=W/name
    artifacts.append({'path':str(p),'sha256':digest(p),'bytes':p.stat().st_size})
(E/'runner-source-pins.json').write_text(json.dumps(artifacts,indent=2)+'\n')
print('pinned union objects',len(rows))
