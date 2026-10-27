from pathlib import Path
import json,hashlib,shutil,os
B=Path(__file__).resolve().parent
assert str(B)=='/home/dombarker/project-offloads/codex-cx-extraction-repro7-20261027'
live=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  args=(p/'cmdline').read_bytes().split(b'\0');name=Path(os.fsdecode(args[0])).name
 except (OSError,IndexError):continue
 if name in ['cbmc','kani-driver','kani-compiler','cargo-kani','lean','lake','charon','charon-driver','aeneas-b59d5188-extended'] and any(str(B).encode() in a for a in args):live.append(dict(pid=p.name,args=[os.fsdecode(a) for a in args]))
assert not live,live
objects=[]
for p in sorted(B.glob('XRg_Association.*')):
 if p.suffix in ['.olean','.ilean','.ir','.private','.server']:
  objects.append(dict(path=str(p),sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size));p.unlink()
removed=[]
for name in ['XRg_01_release_target','XRg_kani_target']:
 p=B/name
 if p.is_dir():shutil.rmtree(p);removed.append(str(p))
report=dict(live_own_provers=live,removed_owned_cache_directories=removed,removed_compiled_objects=objects,retained='All source/receipt/log/LLBC/tool artifacts, crate lockfile, coherent shared workspace/cache and all keys untouched',solver_temp_policy='No timeout or killed Kani run; own solver/build scratch under XRg_kani_target is removed. No unidentified shared /tmp file is deleted.')
(B/'XRg_Cleanup.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
