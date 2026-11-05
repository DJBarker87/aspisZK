from pathlib import Path
import json,hashlib,re,subprocess,difflib
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';p=E/'NGW_NATIVE_INPUTS.json';x=json.loads(p.read_text());s=x[C+'NGW_new.rs']
a=s.index('fn box_exercise(');b=s.index('\ngate!(box_g0',a);before=s[a:b]
for name in ['k','d','term','limb']:
 s=s.replace(f'let {name}:usize=kani::any();',f'let {name}:usize=if cfg!(NGW_invert)&&g==1{{0}}else{{kani::any()}};',1 if False else 0) if False else s
# Restrict only the negative-control observation index; positive execution is identical.
chunk=before
for name in ['k','d','term','limb']:
 old=f'let {name}:usize=kani::any();';new=f'let {name}:usize=if cfg!(NGW_invert)&&g==1{{0}}else{{kani::any()}};';assert old in chunk;chunk=chunk.replace(old,new)
normalize=lambda t:re.sub(r'if cfg!\(NGW_invert\)&&g==1\{0\}else\{kani::any\(\)\}', 'kani::any()',t)
assert normalize(chunk)==before
s=s[:a]+chunk+s[b:];x[C+'NGW_new.rs']=s;p.write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NGW_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()});(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
(E/'NGW_BOX_CONTROL_SPLIT.json').write_text(json.dumps(dict(old='NGW_K082 (excluded 90s timeout)',positive='NGW_K081 (reused, no rerun)',new_control='NGW_K089',change='negative-only index selection set to0 for k/d/term/limb; boxed inputs remain fully arbitrary; corrupt the actual boxed factor word',same_positive_body_after_cfg_false=True,positive_body_sha256=hashlib.sha256(before.encode()).hexdigest(),normalized_new_body_sha256=hashlib.sha256(normalize(chunk).encode()).hexdigest(),same_name='weights::NGW_new::box_g1',new_trust=False),indent=2)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
