from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';p=E/'NHV_NATIVE_INPUTS.json';x=json.loads(p.read_text());x[C+'NHV_native.rs']=(E/'NHV_native.rs.txt').read_text();p.write_text(json.dumps(x,indent=1)+'\n')
(E/'NHV_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()},indent=2)+'\n')
patch=''
for n,t in x.items():
 old='' if 'NHV_' in n else subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],text=True)
 if old!=t:patch+=''.join(difflib.unified_diff(old.splitlines(True),t.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
(E/'NHV_HARNESSES.patch').write_text(patch)
