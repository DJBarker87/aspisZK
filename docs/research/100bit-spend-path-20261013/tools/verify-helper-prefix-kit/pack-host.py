from pathlib import Path
import tarfile,hashlib,json,io
E=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-verify-prefix-fe80-20261017');W=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-verify-prefix-proof-20261017');out=W/'verify-helper-prefix-accepted.tar.gz';items={}
def addroot(root,prefix):
 for p in root.rglob('*'):
  if not p.is_file() or p.is_symlink():continue
  rel=p.relative_to(root)
  if any(c in {'target','import-overlay','.lake','__pycache__'} for c in rel.parts):continue
  items[prefix+str(rel)]=p.read_bytes()
addroot(E,'prefix-extraction/');addroot(W/'sources','proof/sources/');addroot(W/'objects','proof/objects/');addroot(W/'successful-targets','proof/successful-targets/');addroot(W/'runs','proof/runs/');addroot(W/'checkpoint-three','proof/checkpoint-three/');addroot(W/'checkpoint-binding-original','proof/checkpoint-binding-original/')
for p in W.iterdir():
 if p.is_file() and p.suffix in {'.py','.json','.log'}:items['proof/'+p.name]=p.read_bytes()
# Exact producing predecessor receipts and narrow parser sources retained; cache
# object bytes are pinned in external snapshot and prior accepted archive.
P=Path('/home/dombarker/project-offloads/aspis-r1-worker-c-tx1-proof-20261016');Q=Path('/home/dombarker/project-offloads/aspis-r1-r18-prefix-20261016/lean-bridge')
for root,prefix,names in [(P,'predecessor-current/',['AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','ExtractedPreparedModel','ExtractedTx1Model','ExtractedTx1Reachability']),(Q,'predecessor-parser/',['AspisR1PrefixAggregateParser.Types','AspisR1PrefixAggregateParser.Funs'])]:
 for n in names:
  stem=n.replace('.','/')
  for f in [root/'sources'/(stem+'.lean'),root/'objects'/(stem+'.olean')]:items[prefix+str(f.relative_to(root))]=f.read_bytes()
  if root==P:
   p=root/'successful-targets'/(n+'.json');items[prefix+str(p.relative_to(root))]=p.read_bytes()
  else:
   phase='types-bridge-a' if n.endswith('Types') else 'funs-bridge-a'
   for p in (root/'runs'/phase).iterdir():
    if p.is_file():items[prefix+str(p.relative_to(root))]=p.read_bytes()
   p=root/('input-manifest-'+phase+'.json');items[prefix+p.name]=p.read_bytes()
records={n:hashlib.sha256(b).hexdigest() for n,b in items.items()};items['SHA256SUMS.json']=(json.dumps(records,indent=2,sort_keys=True)+'\n').encode()
with tarfile.open(out,'w:gz') as tar:
 for n,b in sorted(items.items()):
  ti=tarfile.TarInfo(n);ti.size=len(b);ti.mtime=0;ti.mode=0o644;tar.addfile(ti,io.BytesIO(b))
print(json.dumps({'archive':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'bytes':out.stat().st_size,'members':len(items)}))
