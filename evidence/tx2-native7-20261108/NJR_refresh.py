from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;n='crates/aspis-r1-cost-probe/src/NJR_parent.rs'
p=E/'NJR_NATIVE_INPUTS.json';x=json.loads(p.read_text());x[n]=(E/'NJR_parent.rs.txt').read_text();p.write_text(json.dumps(x,indent=2)+'\n')
p=E/'NJR_SOURCE_PINS.json';pins=json.loads(p.read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items() if n.startswith(('crates/','programs/'))});p.write_text(json.dumps(pins,indent=2)+'\n')
patch=''
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],capture_output=True,text=True);old=r.stdout if r.returncode==0 else ''
 patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n,tofile='b/'+n))
(E/'NJR_native.patch').write_text(patch)
