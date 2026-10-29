"""Own workspace-only cache export / build scratch cleanup; never remove caches or keys."""
from pathlib import Path
import json,hashlib,shutil,os
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-leaves-20261029')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-q-leaves-cache-20261029')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
active=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  cwd=(p/'cwd').resolve();cmd=(p/'cmdline').read_bytes().replace(b'\0',b' ').decode(errors='replace')
 except (OSError,FileNotFoundError):continue
 if str(cwd).startswith(str(B)) and any(w in cmd for w in ['/lean ','/cargo-kani ','/charon ','/aeneas-b59','S2W_run_host.py NEA_']):active.append({'pid':p.name,'cwd':str(cwd),'command':cmd})
assert not active,active
exports={};destroot=C/'NEA_exports_20261029';destroot.mkdir(exist_ok=True)
for p in (B/'NEA_objects').rglob('*'):
 if not p.is_file():continue
 rel=p.relative_to(B/'NEA_objects');assert rel.parts[0].startswith('NEA_'),rel
 dest=destroot/rel;dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():assert sha(dest)==sha(p),('Do not overwrite an existing distinct cache object',str(dest))
 else:shutil.copy2(p,dest)
 exports[str(rel)]={'path':str(dest),'sha256':sha(dest),'bytes':dest.stat().st_size}
artifacts={}
for root in ['NEA_target','NEA_ref_target']:
 for p in (B/root).rglob('*'):
  if p.is_file() and (p.name.endswith(('.kani-metadata.json','.symtab.out')) or p.suffix=='.out'):
   artifacts[str(p.relative_to(B))]={'sha256':sha(p),'bytes':p.stat().st_size}
removed=[];retained_key_markers=[]
for name in ['NEA_target','NEA_ref_target','NEA_tmp','NEA_objects']:
 p=B/name
 if not p.exists():continue
 markers=[str(f) for f in p.rglob('*') if f.is_file() and (f.name.endswith('-keypair.json') or 'wallet' in f.name.lower() and f.suffix=='.json')]
 if markers:retained_key_markers+=markers;continue
 assert p.parent==B and p.name in ['NEA_target','NEA_ref_target','NEA_tmp','NEA_objects']
 shutil.rmtree(p);removed.append(str(p))
result={'active_own_builds':active,'cache_path':str(C),'export_root':str(destroot),'exports':exports,'deleted_only_rebuildable_own_scratch':removed,'retained_key_markers':retained_key_markers,'no_wallet_or_account_key_deleted':True,'cache_retained':True,'native_artifact_hashes_before_scratch_cleanup':artifacts}
(B/'NEA_HOST_FINISH.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
