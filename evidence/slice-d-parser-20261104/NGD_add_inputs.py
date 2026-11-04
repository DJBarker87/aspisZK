"""Own sidecar edits only; emits a retained patch and updates source pins."""
from pathlib import Path
import json,hashlib,difflib,sys,subprocess
E=Path(__file__).resolve().parent

def update(files,label):
 p=E/'NGD_NATIVE_INPUTS.json';old=json.loads(p.read_text());patch=[]
 for n,t in files.items():
  existed=n in old
  if existed: before=old[n]
  else:
   result=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],capture_output=True,text=True)
   existed=result.returncode==0;before=result.stdout if existed else ''
  patch+=difflib.unified_diff(before.splitlines(True),t.splitlines(True),fromfile='a/'+n if existed else '/dev/null',tofile='b/'+n)
 old.update(files);p.write_text(json.dumps(old,indent=1)+'\n')
 pins=json.loads((E/'NGD_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()});(E/'NGD_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');(E/(label+'.patch')).write_text(''.join(patch))
 complete=[]
 for n,t in old.items():
  result=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],capture_output=True,text=True);before=result.stdout if result.returncode==0 else ''
  complete+=difflib.unified_diff(before.splitlines(True),t.splitlines(True),fromfile='a/'+n if result.returncode==0 else '/dev/null',tofile='b/'+n)
 (E/'NGD_COMPLETE.patch').write_text(''.join(complete))
