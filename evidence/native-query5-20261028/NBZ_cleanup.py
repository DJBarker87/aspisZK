from NBZ_host import *
import fcntl
_serial=(E/'NBZ_SERIAL.lock').open('a');fcntl.flock(_serial,fcntl.LOCK_EX)
assert len(list(E.glob('NBZ_K[0-9][0-9][0-9]/receipt.json')))==90
code=f'''from pathlib import Path
import json,hashlib,shutil,os
b=Path({B!r});live=[]
for p in Path('/proc').iterdir():
 if not p.name.isdigit():continue
 try:
  exe=(p/'exe').resolve().name;cmd=(p/'cmdline').read_bytes().replace(b'\\0',b' ').decode();cwd=str((p/'cwd').resolve())
  if exe in ['cbmc','cadical','kissat','rustc','cargo','cargo-kani','kani-compiler','lean','lake'] and (str(b) in cmd or cwd==str(b)):live.append(dict(pid=int(p.name),exe=exe,command=cmd))
 except (OSError,UnicodeDecodeError):pass
assert not live,live
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for part in iter(lambda:f.read(1048576),b''):h.update(part)
 return h.hexdigest()
removed=[]
for p in (b/'NBZ_tmp').rglob('*'):
 if p.is_file() and ((p.name.startswith('external-sat') and p.suffix=='.cnf') or p.name.startswith('smt2_dec_problem')):
  removed.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)));p.unlink()
target=b/'NBZ_target';assert not target.is_symlink();size=sum(p.stat().st_size for p in target.rglob('*') if p.is_file()) if target.exists() else 0
if target.exists():shutil.rmtree(target)
cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028');assert cache.is_dir()
tools={{}}
for root in [Path('/home/dombarker/.kani/kani-0.67.0/bin'),Path('/home/dombarker/.kani/kani-0.67.0/toolchain/bin')]:
 if root.exists():
  for p in root.iterdir():
   if p.is_file() and p.name in ['cbmc','cargo-kani','kani-compiler','kani-driver','rustc','cargo','cadical','kissat']:tools[str(p)]=dict(resolved=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p))
p=Path('/home/dombarker/.cargo/bin/cargo-kani')
if p.exists():tools[str(p)]=dict(resolved=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p))
print(json.dumps(dict(no_live_own_prover_processes=True,solver_removed=removed,target_removed_bytes=size,cache_retained=str(cache),scratch_retained=str((b/'NBZ_src').resolve()),tools=tools,no_key_actions=True),indent=2))
'''
r=py(code);assert r.returncode==0,r.stderr
(E/'NBZ_CLEANUP.json').write_text(r.stdout)
# Preserve every attempted Lean source, including excluded drafts, as text.
r=py(f'''from pathlib import Path
import json
b=Path({B!r});out={{}}
for p in b.glob('NBZ_L[0-9][0-9][0-9]/sources/NBZ_generated/NBZ_*.lean'):out[str(p.relative_to(b))]=p.read_text()
print(json.dumps(out))
''');assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():p=E/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
print('Own proof processes terminal; target removed; shared/persistent caches retained; Lean snapshots collected')
