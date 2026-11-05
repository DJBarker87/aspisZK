from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';inputs=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());s=inputs[C+'NGM_verifier.rs']
old='fn anye()->E{E::new(anyk(),anyk())}'
new='fn anye()->E{let limbs:[u32;8]=kani::any();for x in limbs{kani::assume(x<0x7fffffff);}E::from_limbs(limbs).unwrap()}'
assert s.count(old)==1;s=s.replace(old,new)
inputs[C+'NGM_verifier.rs']=s;(E/'NGM_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n');pins=json.loads((E/'NGM_SOURCE_PINS.json').read_text());pins[C+'NGM_verifier.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else'/dev/null',tofile='b/'+n)
(E/'NGM_harness.patch').write_text(''.join(patch))
s=(E/'NGM_queue5.py').read_text().replace('for group in range(14):','for group in range(1,8):').replace('55+2*group','85+2*group').replace("f'verifier::NGM_dot::finish_g{group:02}'","f'verifier::NGM_verifier::finish_control_{group}'")
(E/'NGM_queue8.py').write_text(s)
with (E/'NGM_FINDINGS.md').open('a')as f:f.write('\nF6: K086 order fragment timed out90s,3.44GiB,swap0. No credit. Isolated setup normalization: anyE formerly E::new(anyk(),anyk()) unnecessarily performed eight modulo-P reductions on already canonical limbs. Replacement generates eight canonical limbs and uses the checked exact decoder E::from_limbs; identical canonical E domain, no product and no increased cap/timeout. K087..100 are seven matched groups1..7 on that simpler shape. K084/085 retain the full Result pair on the prior shape. No renamed timed-out harness.\n')
