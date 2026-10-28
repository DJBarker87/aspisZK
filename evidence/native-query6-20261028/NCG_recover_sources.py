from NCG_host import *
import difflib
for a in sorted(E.glob('NCG_K[0-9][0-9][0-9].json')):
 name=a.stem
 r=py(f"from pathlib import Path;print((Path({B!r})/{name!r}/'sources/NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs').read_text(),end='')")
 assert r.returncode==0,r.stderr
 (E/(name+'-harness.patch')).write_text(''.join(difflib.unified_diff([],r.stdout.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NCG_native.rs')))
