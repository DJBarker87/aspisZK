from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/';x=json.loads((E/'NGW_NATIVE_INPUTS.json').read_text());s=x[C+'NGW_new.rs'];assert 'struct PrefixLog'not in s
s+=r'''
struct PrefixLog{reply:[[K;10];3],arg:[K;10],ptr:*const K,calls:usize}
fn point_call(alpha:&[K;10],log:&mut PrefixLog)->[[K;10];3]{log.arg=*alpha;log.ptr=alpha.as_ptr();log.calls+=1;log.reply}
fn prefix(alpha:&[K;10],log:&mut PrefixLog)->([[K;10];3],[K;2],Factors){let points=point_call(alpha,log);let extra=[alpha[8],alpha[9]];let factors=[[[K::ZERO;4];5];5];(points,extra,factors)}
fn prefix_exercise(g:u8){let alpha=core::array::from_fn(|_|q(kani::any()));let reply=core::array::from_fn(|_|core::array::from_fn(|_|q(kani::any())));let mut log=PrefixLog{reply,arg:[K::ZERO;10],ptr:core::ptr::null(),calls:0};let (points,mut extra,factors)=prefix(&alpha,&mut log);let p:usize=kani::any();kani::assume(p<3);let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<2);let k:usize=kani::any();kani::assume(k<5);let d:usize=kani::any();kani::assume(d<5);let term:usize=kani::any();kani::assume(term<4);let limb:usize=kani::any();kani::assume(limb<4);
 if cfg!(NGW_invert){if g==0{log.ptr=log.ptr.wrapping_add(1);}else{let mut w=words(extra[j]);w[limb]^=1;extra[j]=q(w);}}
 assert!(if g==0{log.calls==1&&log.ptr==alpha.as_ptr()&&words(log.arg[i])[limb]==words(alpha[i])[limb]}else{words(points[p][i])[limb]==words(reply[p][i])[limb]&&words(extra[j])[limb]==words(alpha[8+j])[limb]&&words(factors[k][d][term])[limb]==0});}
gate!(prefix_g0,prefix_exercise,0);
gate!(prefix_g1,prefix_exercise,1);
'''
x[C+'NGW_new.rs']=s;(E/'NGW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NGW_SOURCE_PINS.json').read_text());pins.update({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()});(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
