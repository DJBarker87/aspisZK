from NBF_host import *
import hashlib
admit('NBF_SETUP001')
r=py("""from pathlib import Path
import json,hashlib,shutil,subprocess
b=Path('/home/dombarker/project-offloads/codex-cx-native-query2-20261027'); old=Path('/home/dombarker/project-offloads/codex-cx-native-query1-20261027')
for n in ['S2W_lean_host.py','S2W_run_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:
 if not (b/n).exists():shutil.copyfile(old/n,b/n)
cache=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027');cache.mkdir(exist_ok=True)
pins={str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}
(b/'NBF_CACHE_START.json').write_text(json.dumps(pins,indent=2)+'\\n')
src=b/'NBF_src'
assert not src.exists(),'scratch already exists'
shutil.copytree(old/'NBB_src',src,ignore=shutil.ignore_patterns('target','.git'))
f=src/'crates/aspis-r1-cost-probe/src/verifier.rs';s=f.read_text();marker='\\n#[cfg(kani)] #[path=\"NBB_harness.rs\"] mod NBB_harness;\\n';assert s.endswith(marker);f.write_text(s[:-len(marker)])
(src/'crates/aspis-r1-cost-probe/src/NBB_harness.rs').unlink()
print((b/'NBF_CACHE_START.json').read_text())
""")
assert r.returncode==0,r.stderr
(E/'NBF_CACHE_START.json').write_text(r.stdout)
