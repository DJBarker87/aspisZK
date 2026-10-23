#!/usr/bin/env python3
"""Pin supplemental comparison/census outputs, keeping large maps host-only."""
import hashlib,json,shlex,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023';H='/home/dombarker/project-offloads/codex-cx-s10-repin3-20261023';REMOTE='dombarker@100.108.41.90'
paths=['alias-mir-diff.json','declaration-ownership.json','declaration-owners.jsonl','changed-declaration-ownership.json']
code='from pathlib import Path; import hashlib,json; H=Path('+repr(H)+'); print(json.dumps([dict(path=str(H/s),sha256=hashlib.sha256((H/s).read_bytes()).hexdigest(),bytes=(H/s).stat().st_size) for s in '+repr(paths)+']))'
rows=json.loads(subprocess.check_output(['ssh',REMOTE,'python3 -c '+shlex.quote(code)],text=True));p=E/'diff-manifest.json';x=json.loads(p.read_text())
newpaths={r['path'] for r in rows}
x['artifacts']=[r for r in x['artifacts'] if r['path'] not in newpaths]
x['host_only']=[r for r in x['host_only'] if r['path'] not in newpaths]
for r in rows:
 if r['bytes']<=5_000_000:
  dest=E/Path(r['path']).name;subprocess.run(['scp','-q',REMOTE+':'+r['path'],str(dest)],check=True)
  assert hashlib.sha256(dest.read_bytes()).hexdigest()==r['sha256']
 else:x['host_only'].append(r)
 x['artifacts'].append(r)
p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n');print('extra pins',len(rows))
