from KNB_host import *
admit('KNB_SETUP001')
code = """from pathlib import Path
import shutil,json
b=Path('/home/dombarker/project-offloads/codex-cx-kani-diag2-20261028')
cache=Path('/home/dombarker/project-offloads/codex-cx-kdiag2-cache-20261028')
if not cache.exists():shutil.copytree('/home/dombarker/project-offloads/codex-cx-query-cache-20261028',cache)
src=b/'KNB_src'
if not src.exists():shutil.copytree('/home/dombarker/project-offloads/codex-cx-native-query3-20261028/NBO_src',src,ignore=shutil.ignore_patterns('target','.git'))
# Restore the exact K042 captured inputs, not the mutable shared source.
frozen=Path('/home/dombarker/project-offloads/codex-cx-native-query5-20261028/NBZ_K042/sources/NBZ_src')
for p in frozen.rglob('*'):
 if p.is_file():shutil.copy2(p,src/p.relative_to(frozen))
p=src/'crates/aspis-r1-cost-probe/src'
# KNB module is a prefix-only rename of the K042 source.
(p/'KNB_native.rs').write_text((p/'NBZ_native.rs').read_text().replace('NBZ_','KNB_'))
f=p/'candidate.rs';f.write_text(f.read_text()+chr(10)+'#[cfg(kani)] #[path="KNB_native.rs"] mod KNB_native;'+chr(10))
(b/'KNB_tmp').mkdir(exist_ok=True)
print(json.dumps(dict(source=str(src),cache=str(cache))))
"""
r=py(code);(E/'KNB_SETUP-result.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2));assert r.returncode==0,r.stderr
payload=json.loads((E.parent/'native-query5-20261028/NBZ_LAUNCHER_INPUTS.json').read_text())
r=py('from pathlib import Path\nimport json\nb=Path('+repr(B)+')\nfor n,s in '+repr(payload)+'.items():\n (b/n).write_text(s)');assert r.returncode==0,r.stderr
