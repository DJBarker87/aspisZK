from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;P='crates/aspis-r1-cost-probe/src/NGM_verifier.rs';inputs=json.loads((E/'NGM_NATIVE_INPUTS.json').read_text());s=inputs[P]
s=s.replace('let expected=reference::finish_ref','let mut expected=reference::finish_ref')
s=s.replace('round0:encode(log.r0),round1:', 'round0:if cfg!(NGM_invert)&&group==0{match encode(log.r0){Ok(_)=>Err(0),Err(e)=>Err(if e==0{1}else{0})}}else{encode(log.r0)},round1:')
old=' let good=match group{'
new=''' if cfg!(NGM_invert){match group{
 1=>expected.len=if expected.len==7{6}else{expected.len+1},
 2=>log.events[0]=255,
 3=>if let Some(x)=&mut log.rounds[0]{x.ptr=x.ptr.wrapping_add(1);},
 4=>if let Some(x)=&mut log.rounds[1]{x.ptr=x.ptr.wrapping_add(1);},
 5=>if let Some(x)=&mut log.new_args{x.1=x.1.wrapping_add(1);},
 6=>if let Some(x)=&mut log.pair_args{x.alpha=x.alpha.wrapping_add(1);},
 7=>if let Some(x)=&mut log.dot_args{x.weights=x.weights.wrapping_add(1);},_=>{}}}
 let good=match group{'''
assert s.count(old)==1;s=s.replace(old,new).replace('assert!(good != cfg!(NGM_invert));','assert!(good);')
inputs[P]=s;(E/'NGM_NATIVE_INPUTS.json').write_text(json.dumps(inputs,indent=1)+'\n')
pins=json.loads((E/'NGM_SOURCE_PINS.json').read_text());pins[P]=hashlib.sha256(s.encode()).hexdigest();(E/'NGM_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n)
(E/'NGM_harness.patch').write_text(''.join(patch))
(E/'NGM_CONTROL_STRENGTHENING.md').write_text('''# Native caller control review

K005..K022 are preliminary source-fission diagnostics. Their inverted assertions fail, but that can witness an unreached optional argument. They are not used as the final ruling-(y) argument controls. Replacement preserves the same harness names and actual caller property; it corrupts the first cached child reply for Result, one recorded argument for argument probes, or one call-count/tag for order probes. Optional argument controls keep the absent-call branch true, so failure must occur at the reached corrupted argument. No timeout or memory failure triggered this change; no verdict is repaired by renaming. K023..K040 are the strengthened pairs, including the one family rename-stability pair required by (ae).
''')
