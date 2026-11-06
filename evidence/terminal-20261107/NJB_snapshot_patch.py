from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json
b=Path('/home/dombarker/project-offloads/codex-cx-terminal-20261107');s=b/'NJB_src';pins=json.loads((b/'NJB_SOURCE_PINS.json').read_text());old=json.loads((b/'NJB_FROZEN_FILE_PINS.json').read_text());print(json.dumps({q:(s/q).read_text()for q in pins if q not in old or pins[q]!=old[q]}))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;files=json.loads(r.stdout);patch='';pins=[]
for q,t in sorted(files.items()):
 if 'KMX'in q:continue
 before=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+q],capture_output=True,text=True);orig=before.stdout if before.returncode==0 else''
 patch+=''.join(difflib.unified_diff(orig.splitlines(True),t.splitlines(True),fromfile='a/'+q if before.returncode==0 else'/dev/null',tofile='b/'+q))
 pins.append(dict(path=q,sha256=hashlib.sha256(t.encode()).hexdigest(),frozen_exists=before.returncode==0))
(E/'NJB_native.patch').write_text(patch);(E/'NJB_PATCH_FILES.json').write_text(json.dumps(pins,indent=1));print(json.dumps(dict(files=len(pins),patch_bytes=len(patch))))
