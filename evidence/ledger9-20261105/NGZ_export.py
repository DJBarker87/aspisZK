"""Retain own compiled exports; pin the actually resolved combined closure."""
from pathlib import Path
import subprocess,json,lzma,hashlib,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90'
B='/home/dombarker/project-offloads/codex-cx-ledger9-20261105';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NGZ_flat'
modules=[json.loads(l)['module'] for l in (E/'NGZ_LOADED_scan.jsonl').read_text().splitlines()]
code='''from pathlib import Path
import json,hashlib,shutil,lzma,subprocess
b=Path(B);c=Path(C);exp=c/'NGZ_exports_20261105';exp.mkdir(exist_ok=True);native=c/'NGZ_native_20261105';native.mkdir(exist_ok=True);out=[]
for directory,dest in [(b/'NGZ_objects',exp),(b/'NGZ_native',native)]:
 for p in directory.iterdir():
  if not p.is_file():continue
  q=dest/p.name
  if not q.exists():shutil.copy2(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  out.append(dict(path=str(q),sha256=h,bytes=q.stat().st_size))
cfg=json.loads((b/'NGZ_L003.json').read_text());roots=cfg['env']['LEAN_PATH'].split(':');pins=[]
for mod in modules:
 rel=mod.replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p,mod
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=mod,path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins)).encode();(b/'NGZ_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(b/'NGZ_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
report=dict(cache_retained=str(c),workspace_retained=str(b),exports=out,closure_sha256=hashlib.sha256(raw).hexdigest(),disk=subprocess.check_output(['df','-h',str(c)],text=True),cache_size=subprocess.check_output(['du','-sh',str(c)],text=True))
(b/'NGZ_EXPORT.json').write_text(json.dumps(report,indent=1)+'\\n');print(json.dumps(dict(exports=len(out),closure_objects=len(pins),cache_size=report['cache_size'])))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nmodules='+repr(modules)+'\n'+code,text=True,capture_output=True)
(E/'NGZ_EXPORT_TRANSPORT.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr;print(r.stdout)
for n in ['NGZ_EXPORT.json','NGZ_CLOSURE_PINS.json.xz','NGZ_CLOSURE_PINS.json.sha256']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
