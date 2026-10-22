#!/usr/bin/env python3
"""Copy and hash all Lean companions of the selected local cache objects."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
ap=argparse.ArgumentParser()
ap.add_argument('plan',type=Path)
ap.add_argument('staging',type=Path)
args=ap.parse_args()
plan=json.loads(args.plan.read_text())
rows=[]
for r in plan['cache_pins']:
    p=Path(r['path'])
    base=args.staging/'retained-objects'/(r['module'].replace('.','/')+'.olean')
    for source,target in [(Path(str(p)+s),Path(str(base)+s)) for s in ['.private','.server']] + [(p.with_suffix('.ir'),base.with_suffix('.ir'))]:
        if source.is_file():
            target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(source,target)
            rows.append({'module':r['module'],'source':str(source),'target':str(target.relative_to(args.staging)),
                         'sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'bytes':source.stat().st_size})
(args.staging/'companion-pins.json').write_text(json.dumps(rows,indent=2,sort_keys=True)+'\n')
print('selected cache companions',len(rows),'bytes',sum(r['bytes'] for r in rows))
