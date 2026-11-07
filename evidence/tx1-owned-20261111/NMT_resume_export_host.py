"""Final OWN workspace export/hash/retention inspection; no shared writes/deletes."""
from pathlib import Path
import json,hashlib,shutil,lzma,os
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert B==Path('/home/dombarker/project-offloads/codex-cx-tx1-owned-20261111')
current=json.loads((B/'NMT_RESUME_MODULES.json').read_text())
export=B/'NMT_resume_exports_20261111';export.mkdir(exist_ok=True);files=[]
for module in current['modules']+['NMT_RESUME_COMBINED_IMPORT','NMT_ProofDriver']:
 p=B/'NMT_objects'/Path(module.replace('.','/')+'.olean');assert p.is_file(),module
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  rel=z.relative_to(B/'NMT_objects');q=export/rel;q.parent.mkdir(parents=True,exist_ok=True)
  shutil.copy2(z,q);assert sha(q)==sha(z)
  files.append(dict(path=str(q),relative=str(rel),sha256=sha(q),bytes=q.stat().st_size))
seeds=json.loads(lzma.decompress((B/'NMT_CACHE_IMPORTS.json.xz').read_bytes()))
for f in seeds['files']:
 assert sha(Path(f['destination']))==f['sha256']
# Pin the Aeneas objects ACTUALLY resolved by the current LEAN_PATH.
roots=os.environ['LEAN_PATH'].split(':');rels=set();pins=[]
for root in roots:
 for stem in ['Aeneas','AeneasMeta']:
  p=Path(root)/stem
  if p.is_dir():rels.update(str(z.relative_to(root))for z in p.rglob('*.olean'))
  if Path(root,stem+'.olean').is_file():rels.add(stem+'.olean')
for rel in sorted(rels):
 p=next(Path(root)/rel for root in roots if (Path(root)/rel).is_file())
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(path=str(z),sha256=sha(z),bytes=z.stat().st_size))
manifest=json.loads((B/'NMT_STAGING_MANIFEST.json').read_text())
for rel,info in manifest['files'].items():assert sha(B/'NMT_src'/rel)==info['sha256'],rel
stdlib=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
launcher={}
for name in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 assert sha(B/name)==sha(stdlib/name),name
 launcher[name]=sha(B/name)
retention=dict(workspace=str(B),workspace_bytes=sum(p.stat().st_size for p in B.rglob('*')if p.is_file()),free_bytes=shutil.disk_usage(B).free,deleted_files=0,seeds_rehashed=len(seeds['files']),frozen_files_rehashed=len(manifest['files']),aeneas_objects=len(pins),launcher_pins=launcher,cache_policy='Retained; no deletion; other workspaces read-only')
assert retention['free_bytes']>=40_000_000_000
assert retention['workspace_bytes']<30_000_000_000
for name,value in [('NMT_RESUME_EXPORT.json',dict(export=str(export),files=files)),('NMT_RESUME_AENEAS_PINS.json',pins),('NMT_RESUME_RETENTION.json',retention)]:
 (B/name).write_text(json.dumps(value,indent=1)+'\n')
print(json.dumps(dict(export_files=len(files),**retention)),flush=True)
