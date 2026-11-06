from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;p=E/'NJJ_NATIVE_INPUTS.json';x=json.loads(p.read_text())
x['crates/aspis-r1-cost-probe/src/NJJ_parent.rs']=(E/'NJJ_parent.rs.txt').read_text();p.write_text(json.dumps(x,indent=2)+'\n');p=E/'NJJ_SOURCE_PINS.json';pins=json.loads(p.read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()});p.write_text(json.dumps(pins,indent=2)+'\n')
patch=''
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],capture_output=True,text=True);old=r.stdout if r.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJJ_native.patch').write_text(patch)
