"""Remove only hash-verified, exported NGZ rebuildable workspace outputs."""
from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-ledger9-20261105';H='dombarker@100.108.41.90'
graphs={p.name.removeprefix('NGZ_').removesuffix('.sha256'):p.read_text().strip()for p in E.glob('NGZ_NEP_*_REACHABLE.txt.sha256')}
code='''from pathlib import Path
import hashlib,json,subprocess
b=Path(B);removed=[];export=json.loads((b/'NGZ_EXPORT.json').read_text());pins={Path(x['path']).name:x for x in export['exports']}
for directory in ['NGZ_objects','NGZ_native']:
 for p in (b/directory).iterdir():
  if not p.is_file():continue
  x=pins.get(p.name)
  if not x:continue
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==x['sha256']==hashlib.sha256(Path(x['path']).read_bytes()).hexdigest()
  removed.append(dict(path=str(p),retained=x['path'],bytes=p.stat().st_size,sha256=h));p.unlink()
for name,h in graphs.items():
 p=b/name
 if p.is_file():
  assert hashlib.sha256(p.read_bytes()).hexdigest()==h;removed.append(dict(path=str(p),retained='local compressed evidence + uncompressed SHA256',bytes=p.stat().st_size,sha256=h));p.unlink()
ps=subprocess.check_output(['ps','-eo','pid,args'],text=True)
active=[s for s in ps.splitlines()if B in s and any(k in s for k in ['/bin/lean ','/bin/leanc ','NGZ_native/NGZ_ProofDriver','NGZ_native/NGZ_Driver'])];assert not active,active
launchers={n:hashlib.sha256((b/n).read_bytes()).hexdigest()for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']}
(b/'NGZ_HOST_END.json').write_text(json.dumps(dict(removed_rebuildable=removed,cache_retained=True,keys_touched=False,active_own_provers=active,unchanged_launcher_pins=launchers,disk=subprocess.check_output(['df','-h',str(b)],text=True)),indent=1));print(len(removed))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input='B='+repr(B)+'\ngraphs='+repr(graphs)+'\n'+code,text=True,capture_output=True);(E/'NGZ_CLEANUP_TRANSPORT.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/NGZ_HOST_END.json'],capture_output=True);assert r.returncode==0;(E/'NGZ_HOST_END.json').write_bytes(r.stdout);print('Retained cache; removed only exported rebuildable outputs')
