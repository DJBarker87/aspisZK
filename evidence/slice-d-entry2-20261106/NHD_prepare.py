from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'slice-d-entry-20261105';D='programs/r1-cost-probe/src/'
x=json.loads((P/'NGL_NATIVE_INPUTS.json').read_text());base=dict(x)
x[D+'lib.rs']+='\n#[cfg(kani)]\n#[path="NHD_calibration.rs"]\nmod NHD_calibration;\n'
x[D+'NHD_calibration.rs']=(E/'NHD_calibration.rs.txt').read_text()
(E/'NHD_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
pins=json.loads((P/'NGL_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in x.items()})
(E/'NHD_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+n],capture_output=True,text=True)
 patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n)
(E/'NHD_COMPLETE.patch').write_text(''.join(patch))
