from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';x=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text());s=x[C+'NGW_new.rs'];old='1=>{let mut w=words(out.factors[k][d][term]);w[limb]^=1;out.factors[k][d][term]=q(w)}';new='1=>{out.factors[0][0][0].c0.a.0^=1;}';assert old in s;s=s.replace(old,new)
x[C+'NGW_new.rs']=s;(E/'NGW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NGW_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()});(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NGW_BOX_SCALAR_SPLIT.json').write_text(json.dumps(dict(old='NGW_K089 (180s runner timeout, excluded)',replacement='NGW_K090',change='actual boxed field scalar XOR at fixed factor[0][0][0].c0.a.0; remove the full QM31 read/reconstruction/write from the negative control',domain='all original boxed input words arbitrary; negative observes exactly the corrupt scalar; positive K081 remains unchanged for cfg=false',same_original_name='weights::NGW_new::box_g1',caps_and_timeouts_unchanged=True,credit='OPEN until native failing verdict'),indent=2)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
