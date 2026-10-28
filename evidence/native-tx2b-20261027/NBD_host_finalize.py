"""Read-only pinning plus deletion of this job's compiled/solver scratch only."""
from pathlib import Path
import subprocess,json,shlex
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-native-tx2b-20261027'
code=r'''
from pathlib import Path
import hashlib,json,subprocess,shutil,os
b=Path('/home/dombarker/project-offloads/codex-cx-native-tx2b-20261027')
c=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
processes=subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines()
live=[s for s in processes if s.split(maxsplit=1)[0] != str(os.getpid()) and str(b) in s and any(x in s for x in ['cargo-kani kani','/bin/lean ','S2W_run_host.py NBD_'])]
assert not live,live
hashes={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in c.rglob('*') if p.is_file()}
sourcepins={str(p.relative_to(b)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in (b/'NBD_src').rglob('*') if p.is_file() and p.name in ['Cargo.lock','NBD_registry.rs','NBD_digest.rs','NBD_terminal.rs']}
removed=[]
for name in ['NBD_target','NBD_tmp']:
 p=b/name
 if p.exists():
  assert p.parent==b and not p.is_symlink()
  sizes=sum(f.stat().st_size for f in p.rglob('*') if f.is_file())
  shutil.rmtree(p);removed.append(dict(path=str(p),bytes=sizes))
# The source scratch and persistent Lean cache are retained; never delete the shared cache.
print(json.dumps(dict(cache_end=hashes,source_pins=sourcepins,own_live_commands=live,removed_compiled_solver_scratch=removed,persistent_cache_retained=True),indent=2))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=20',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
(E/'NBD_FINALIZE_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr),indent=2)+'\n')
assert r.returncode==0,r.stdout+r.stderr
x=json.loads(r.stdout);(E/'NBD_CACHE_END.json').write_text(json.dumps(x.pop('cache_end'),indent=2)+'\n');(E/'NBD_HOST_CLEANUP.json').write_text(json.dumps(x,indent=2)+'\n')
