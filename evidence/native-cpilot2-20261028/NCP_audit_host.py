from pathlib import Path
import json,hashlib,difflib,subprocess,shutil
b=Path(__file__).resolve().parent;src=b/'NCP_src';base=json.loads((b/'NCP_FROZEN_MANIFEST.json').read_text())
def pin(p):return {'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size}
changed={n:pin(src/n) for n,v in base.items() if (src/n).is_file() and pin(src/n)!=v}
missing=[n for n in base if not (src/n).is_file()]
added=[str(p.relative_to(src)) for folder in ['crates','programs'] for p in (src/folder).rglob('*') if p.is_file() and str(p.relative_to(src)) not in base]
# Return only changed source files; the Mac performs byte-exact insert-only checks against frozen git.
cache=Path('/home/dombarker/project-offloads/codex-cx-cpilot2-cache-20261028');original=json.loads((b/'NCP_CACHE_IMPORTED.json').read_text())
cache_now={str(p.relative_to(cache)):pin(p) for p in cache.rglob('*') if p.is_file()}
preserved=all(cache_now.get(n,{}).get('sha256')==v['sha256'] for n,v in original.items())
C=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025');roots=[cache,C,C/'objects',Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
keys={'Aeneas.olean'}
for root in roots:
 if (root/'Aeneas').exists():keys.update(str(p.relative_to(root)) for p in (root/'Aeneas').rglob('*.olean'))
libs={}
for key in sorted(keys):
 p=next((r/key for r in roots if (r/key).is_file()),None)
 assert p is not None,key
 libs[key]={'path':str(p),**pin(p)}
procs=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().replace(b'\x00',b' ').decode(errors='replace')
  if str(b) in args and any(x in args for x in ['cargo-kani','cbmc ','bin/lean ','S2W_lean_host.py','S2W_run_host.py']):procs.append({'pid':p.name,'args':args})
 except (FileNotFoundError,PermissionError,ProcessLookupError):pass
out={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','checked_files':len(base),'missing':missing,'changed':changed,'new_scratch_files':added,'source_texts':{n:(src/n).read_text() for n in changed},'new_texts':{n:(src/n).read_text() for n in added},'cache_imports_preserved':preserved,'cache_files':len(cache_now),'resolved_aeneas':libs,'active_own_provers':procs,'cargo_lock':pin(src/'Cargo.lock'),'kmx_patch':pin(b/'NCP_KMX_copy_stubs.patch')}
(b/'NCP_FINAL_HOST_AUDIT.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
