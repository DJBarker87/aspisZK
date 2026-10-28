"""Read actual installed sysroot and resolved dependency sources; no builds."""
from pathlib import Path
import json,lzma,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028'); O=D/'classify-source-capture';O.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
result={'sysroots':{},'dependencies':{},'files':{}}
for cohort,tc in [('evidence','nightly-2026-06-01'),('deployed','1.94.1')]:
 root=Path('/home/dombarker/.rustup/toolchains')/(tc+'-x86_64-unknown-linux-gnu')/'lib/rustlib/src/rust'
 result['sysroots'][cohort]={'root':str(root),'toolchain':tc,'version':(root/'library/Cargo.toml').read_text()[:300]}
 for lib in ['core','alloc','std','stdarch']:
  for p in (root/'library'/lib).rglob('*.rs'):
   b=p.read_bytes();key=cohort+'/'+str(p.relative_to(root));result['files'][key]={'path':str(p),'sha256':sha(b),'text':b.decode()}
for cohort,variant in [('evidence','libraries-charon'),('deployed','libraries-client194-exact')]:
 m=json.loads((D/variant/'metadata.json').read_text());ids={n['id']:n for n in m['resolve']['nodes']}
 for p in m['packages']:
  if p['name'] not in ['zeroize','sha2','digest','block-buffer','generic-array','typenum','cpufeatures']:continue
  root=Path(p['manifest_path']).parent;result['dependencies'][cohort+'/'+p['name']]={'id':p['id'],'root':str(root),'version':p['version'],'features':ids[p['id']]['features']}
  for fp in root.rglob('*.rs'):
   b=fp.read_bytes();key=cohort+'/registry/'+p['name']+'/'+str(fp.relative_to(root));result['files'][key]={'path':str(fp),'sha256':sha(b),'text':b.decode()}
with lzma.open(O/'sources.json.xz','wt') as f:json.dump(result,f)
print('files',len(result['files']),'compressed bytes',(O/'sources.json.xz').stat().st_size)
