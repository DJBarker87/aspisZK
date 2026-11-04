"""Pin unchanged raw walker support and independent import expectations."""
from NFN_remote import *
import hashlib
C='/home/dombarker/project-offloads/codex-cx-slice-q-phase-cache-20261104'
admit('NFN_AUDIT_SUPPORT')
r=ssh('NFN_AUDIT_SUPPORT','python3',f'''from pathlib import Path
import json,hashlib
b=Path({B!r});c=Path({C!r});files={{}}
for name in ['NFA_WALKER.c','NFA_MemoryLimit.c']:
 data=(c/'NFF_native_20261104'/name).read_text();(b/'NFN_native'/name).write_text(data);files[name]=data
print(json.dumps(files))
''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():
 p=E/'NFN_native'/n;p.parent.mkdir(exist_ok=True);p.write_text(s)
# Fixtures are unchanged copied inputs, not new modules or propositions.
(E/'NFN_FIXTURE_PATHS.json').write_text(json.dumps([C+'/fixtures'])+'\n')
g={r['module']:r['imports'] for r in map(json.loads,(E.parent/'slice-q-mul7-20261104/NFF_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
graph=json.loads((E/'NFN_SOURCE_GRAPH.json').read_text())
for n,r in graph.items():
 if n not in g and 'imports' in r:g[n]=list(dict.fromkeys(['Init']+r['imports']))
ng=E.parent/'slice-q-compose6-20261104'
generated=json.loads((ng/'NFG_GENERATED.json').read_text())
for r in json.loads((ng/'NFG_OBJECT_EXPORTS.json').read_text())['objects']:
 n=r['module'];p=ng/(generated[n]['path'] if n in generated else n.replace('.','/')+'.lean')
 assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']
 imports=[m for l in p.read_text().splitlines() if l.startswith('import ') for m in l[7:].split() if m!='all']
 g[n]=list(dict.fromkeys(['Init']+imports))
for p in E.glob('NFN_*.lean'):
 mods=['Init']+[n for line in p.read_text().splitlines() if line.startswith('import ') for n in line[7:].split() if n!='all']
 g[p.stem]=list(dict.fromkeys(mods))
(E/'NFN_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=n,imports=imp))+'\n' for n,imp in sorted(g.items())))
print('audit support pinned')
