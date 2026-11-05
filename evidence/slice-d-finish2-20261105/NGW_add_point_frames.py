from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;core='crates/aspis-core/src/';p=E/'NGW_NATIVE_INPUTS.json';x=json.loads(p.read_text())
s=x[core+'NGW_points.rs'];assert 'struct WrapperLog' not in s
s+=r'''
struct WrapperLog{reply:[[QM31;10];3],args:[QM31;10],ptr:*const QM31,calls:usize}
fn point_reply(alpha:&[QM31;10],log:&mut WrapperLog)->[[QM31;10];3]{log.args=*alpha;log.ptr=alpha.as_ptr();log.calls+=1;log.reply}
fn source_wrapper(alpha:&[QM31;10],log:&mut WrapperLog)->[[QM31;10];3]{point_reply(alpha,log)}
fn wrapper_exercise(g:u8){let alpha=core::array::from_fn(|_|anyq());let before=alpha;let reply=core::array::from_fn(|_|core::array::from_fn(|_|q(kani::any())));let mut log=WrapperLog{reply,args:[QM31::ZERO;10],ptr:core::ptr::null(),calls:0};let out=source_wrapper(&alpha,&mut log);let p:usize=kani::any();kani::assume(p<3);let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<4);
 if cfg!(NGW_invert){match g{0=>{let mut w=words(log.reply[p][i]);w[j]^=1;log.reply[p][i]=q(w)},1=>{let mut w=words(log.args[i]);w[j]^=1;log.args[i]=q(w)},2=>log.ptr=log.ptr.wrapping_add(1),3=>log.calls+=1,_=>{}}}
 assert!(match g{0=>words(out[p][i])[j]==words(log.reply[p][i])[j],1=>words(log.args[i])[j]==words(alpha[i])[j],2=>log.ptr==alpha.as_ptr(),3=>log.calls==1,_=>words(alpha[i])[j]==words(before[i])[j]});}
fn return_points(z:&[QM31;10],successor:[QM31;10],absorption:[QM31;10])->[[QM31;10];3]{[*z,successor,absorption]}
fn return_exercise(g:u8){let z=core::array::from_fn(|_|q(kani::any()));let successor=core::array::from_fn(|_|q(kani::any()));let absorption=core::array::from_fn(|_|q(kani::any()));let out=return_points(&z,successor,absorption);let p:usize=kani::any();kani::assume(p<3);let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<4);let mut expected=words(match p{0=>z[i],1=>successor[i],_=>absorption[i]})[j];if cfg!(NGW_invert){expected^=1;}assert!(words(out[p][i])[j]==expected);let _=g;}
fn init_exercise(g:u8){let z=core::array::from_fn::<_,10,_>(|_|q(kani::any()));let successor=z;let carry=QM31::ONE;let absorption=z;let i:usize=kani::any();kani::assume(i<10);let j:usize=kani::any();kani::assume(j<4);let mut expected=words(z[i])[j];if cfg!(NGW_invert){expected^=1;}assert!(if g==0{words(successor[i])[j]==expected}else{words(absorption[i])[j]==expected});assert!(words(carry)==[1,0,0,0]);}
'''
for i in range(4):s+=f'gate!(wrapper_g{i},wrapper_exercise,{i});\n'
s+='gate!(return_frame,return_exercise,0);\ngate!(init_successor,init_exercise,0);\ngate!(init_absorption,init_exercise,1);\n'
x[core+'NGW_points.rs']=s;p.write_text(json.dumps(x,indent=1)+'\n');pins=json.loads((E/'NGW_SOURCE_PINS.json').read_text());pins[core+'NGW_points.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NGW_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
patch=[]
for n,t in x.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True);patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NGW_harness.patch').write_text(''.join(patch))
