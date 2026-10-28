from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NCL_host as h
code=f'''from pathlib import Path
import json,hashlib,shutil,subprocess,re
b=Path({h.B!r});c=Path('/home/dombarker/project-offloads/codex-cx-tx1top-cache-20261028')
rows=subprocess.check_output(['ps','-eo','args='],text=True).splitlines()
live=[x for x in rows if re.match(r'^(?:/usr/bin/)?python3 S2W_(?:run|lean)_host[.]py NCL_',x.strip())];assert not live,live
p=b/'NCL_src/Cargo.lock';data=p.read_bytes();digest=hashlib.sha256(data).hexdigest();assert digest=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
old=dict(is_symlink=p.is_symlink(),resolved=str(p.resolve()),sha256=digest)
if p.is_symlink():p.unlink();p.write_bytes(data)
assert not p.is_symlink() and p.stat().st_nlink==1
assert hashlib.sha256(p.read_bytes()).hexdigest()==digest
(b/'NCL_gate.py').write_text({(E/'NCL_gate.py').read_text()!r})
removed=[]
for name in ['NCL_target','NCL_tmp']:
 p=b/name
 if p.exists():
  assert not p.is_symlink() and p.parent==b
  files=[q for q in p.rglob('*') if q.is_file()];size=sum(q.stat().st_size for q in files)
  removed.append(dict(path=str(p),files=len(files),bytes=size));shutil.rmtree(p)
assert c.is_dir()
print(json.dumps(dict(prior_lock=old,corrected_lock=dict(path=str(b/'NCL_src/Cargo.lock'),is_symlink=False,sha256=digest),removed_rebuildable_scratch=removed,persistent_cache_retained=str(c),persistent_cache_files=sum(1 for p in c.rglob('*') if p.is_file()),gate_sha256=hashlib.sha256((b/'NCL_gate.py').read_bytes()).hexdigest(),observed_live_own_launchers=live,no_proof_rerun=True)))
'''
r=h.remote_py(code);assert r.returncode==0,r.stdout+r.stderr
(E/'NCL_CLEANUP.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n');print(r.stdout)
