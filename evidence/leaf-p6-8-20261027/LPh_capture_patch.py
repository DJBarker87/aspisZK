from pathlib import Path
import subprocess,json,hashlib,sys
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-leaf-p6-8-20261027'
for a in sys.argv[1:]:
 code='''from pathlib import Path
import json,difflib
B=Path("'''+B+'''"); a="'''+a+'''"
cfg=json.loads((B/(a+".json")).read_text())
base=Path("/home/dombarker/project-offloads/codex-cx-leaf-p6-7-20261027/LPg_src")
for f in cfg["sources"]:
 if not f.startswith("LPh_src/"):continue
 rel=f.removeprefix("LPh_src/"); p=B/a/"sources"/f; q=base/rel
 before=q.read_text().splitlines(True) if q.exists() else []
 after=p.read_text().splitlines(True)
 print("".join(difflib.unified_diff(before,after,fromfile="a/"+rel if q.exists() else "/dev/null",tofile="b/"+rel)),end="")
'''
 r=subprocess.run(['ssh',H,'python3 - <<\'PYREMOTE\'\n'+code+'\nPYREMOTE'],text=True,capture_output=True,check=True)
 data=r.stdout.encode();name=a+'-harness.patch';(E/name).write_bytes(data)
 (E/(a+'-patch.json')).write_text(json.dumps({'patch':name,'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'base':'LPg final scratch: inherited LPa then LPc then LPg patches','boundary':'scratch-only; attrs and harness modules; no shipped changes'},indent=2)+'\n')
