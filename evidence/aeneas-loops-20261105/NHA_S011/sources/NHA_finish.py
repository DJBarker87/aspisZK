"""Export only NHA-owned compiled artifacts, then remove owned rebuildable outputs."""
from pathlib import Path
import hashlib,json,shutil,subprocess
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-transcript-queries-cache-20261104')
D=C/'NHA_exports_20261105';D.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
exports={}
for p in (B/'NHA_objects').rglob('*'):
 if p.is_file():
  rel=p.relative_to(B/'NHA_objects');q=D/rel;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert sha(q)==sha(p),q
  else:shutil.copy2(p,q)
  exports[str(rel)]={'path':str(q),'sha256':sha(q),'bytes':q.stat().st_size}
(B/'NHA_EXPORT.json').write_text(json.dumps({'destination':str(D),'files':exports,'cache_retained':True},indent=2))
# Reused existing owned cache was previously seeded by COPY; preserve original seed receipt.
seed=B/'NHA_REUSED_CACHE_SEED.json';origin=Path('/home/dombarker/project-offloads/codex-cx-transcript-queries-20261105/NGQ_CACHE_IMPORTS.json.xz')
seed.write_text(json.dumps({'owned_cache':str(C),'seed_origin':str(origin),'seed_sha256':sha(origin) if origin.exists() else None,'note':'Existing assigned cache reused read-only. Actually resolved library/import objects are pinned in NHA_L*/receipt.json. No foreign cache modified; no cache deleted.'},indent=2))
if origin.exists():shutil.copy2(origin,B/'NHA_REUSED_NGQ_CACHE_IMPORTS.json.xz')
removed=[]
for n in ['NHA_charon_target','NHA_objects']:
 p=B/n
 if p.exists():shutil.rmtree(p);removed.append(n)
row={'removed_owned_build_outputs':removed,'cache_retained':str(D),'remaining_job_disk':subprocess.check_output(['du','-sh',str(B)],text=True).strip(),'host_disk':subprocess.check_output(['df','-h','/'],text=True),'owned_elf_changes':False,'keys_created_or_deleted':False,'tool_patch_applied':False}
(B/'NHA_HOST_END.json').write_text(json.dumps(row,indent=2));print(json.dumps(row))
