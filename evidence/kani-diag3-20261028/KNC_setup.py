from KNC_host import *
admit('KNC_SETUP001')
code='''from pathlib import Path
import shutil,json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-kani-diag3-20261028')
old=Path('/home/dombarker/project-offloads/codex-cx-kani-diag2-20261028')
cache=Path('/home/dombarker/project-offloads/codex-cx-kdiag3-cache-20261028')
seed=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028')
seeded=not cache.exists()
if seeded:shutil.copytree(seed,cache)
src=b/'KNC_src'
assert not src.exists()
shutil.copytree(old/'KNB_src',src,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
frozen=old/'KNB_K008/sources/KNB_src'
for p in frozen.rglob('*'):
 if p.is_file():shutil.copy2(p,src/p.relative_to(frozen))
for n in ['S2W_run_host.py']:shutil.copy2(old/n,b/n)
(b/'KNC_tmp').mkdir(exist_ok=True)
actual={str(p.relative_to(frozen)):hashlib.sha256((src/p.relative_to(frozen)).read_bytes()).hexdigest() for p in frozen.rglob('*') if p.is_file()}
expected=json.loads((old/'KNB_K008/receipt.json').read_text())['source_hashes']
assert actual=={k.removeprefix('KNB_src/'):v for k,v in expected.items()}
assert (src/'Cargo.lock').read_bytes()==(frozen/'Cargo.lock').read_bytes()
print(json.dumps(dict(source=str(src),restored_source_hashes=actual,exact_K008_snapshot_match=True,cache=str(cache),cache_seed=str(seed),seeded_by_copy=seeded,shared_kmy_cache_untouched=True,launcher_sha256=hashlib.sha256((b/'S2W_run_host.py').read_bytes()).hexdigest(),disk_free_bytes=shutil.disk_usage(b).free),indent=2))
'''
r=py(code);(E/'KNC_SETUP-result.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');assert r.returncode==0,r.stderr
