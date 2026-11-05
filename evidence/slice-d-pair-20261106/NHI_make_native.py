"""Generate committed scratch-only patch; never alter frozen source files."""
from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent; C='crates/aspis-r1-cost-probe/src/'
code=r'''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn q(x:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
fn raw(x:K)->[u32;4]{[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
struct Log{reply:[K;4],left:[[u32;4];4],right:[[u32;4];4],calls:usize}
fn product(x:K,y:K,l:&mut Log)->K{let i=l.calls;l.left[i]=raw(x);l.right[i]=raw(y);l.calls+=1;l.reply[i]}
fn source_window(row:&[K;4],output:&mut[K],j:usize,n:usize,l:&mut Log){
 let x=output[j];
 output[j+0*n]=product(x,row[0],l);
 output[j+1*n]=product(x,row[1],l);
 output[j+2*n]=product(x,row[2],l);
 output[j+3*n]=product(x,row[3],l);
}
fn exercise(g:usize){
 let before:[[u32;4];64]=kani::any();let row_words:[[u32;4];4]=kani::any();let replies:[[u32;4];4]=kani::any();
 let row=core::array::from_fn(|i|q(row_words[i]));let mut output=core::array::from_fn::<K,64,_>(|i|q(before[i]));
 let n:usize=kani::any();kani::assume(n==1||n==4||n==16);let j:usize=kani::any();kani::assume(j<n);
 let frame:usize=kani::any();kani::assume(frame<64);let mut l=Log{reply:core::array::from_fn(|i|q(replies[i])),left:[[0;4];4],right:[[0;4];4],calls:0};
 source_window(&row,&mut output,j,n,&mut l);
 let mut good=if g<16{raw(output[j+(g/4)*n])[g%4]==replies[g/4][g%4]}
 else if g<32{l.left[(g-16)/4][(g-16)%4]==before[j][(g-16)%4]}
 else if g<48{l.right[(g-32)/4][(g-32)%4]==row_words[(g-32)/4][(g-32)%4]}
 else if g<52{if frame!=j&&frame!=j+n&&frame!=j+2*n&&frame!=j+3*n{raw(output[frame])[g-48]==before[frame][g-48]}else{true}}
 else if g==52{l.calls==4}
 else if g==53{j!=j+n&&j+n!=j+2*n&&j+2*n!=j+3*n}
 else if g==54{l.left[3]==before[j]}
 else if g==55{j+3*n<64}
 else if g==56{let mut it=(0..n).rev();let first=it.next();first==Some(n-1)}
 else if g==57{let mut next_n=n;next_n*=4;next_n==4*n}
 else if g==58{let mut ns=[0usize;3];let mut ds=[0usize;3];let mut count=0;let mut width=1;for d in 2..5{ns[count]=width;ds[count]=d;count+=1;width*=4;}count==3&&ns==[1,4,16]&&ds==[2,3,4]&&width==64}
 else{let earlier:usize=kani::any();kani::assume(j<earlier&&earlier<n);j!=earlier&&j+n!=earlier&&j+2*n!=earlier&&j+3*n!=earlier};
 if cfg!(NHI_invert){good=!good;}assert!(good);
}
macro_rules! gate{($name:ident,$n:expr)=>{#[kani::proof]#[kani::unwind(66)]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){exercise($n)}};}
'''
code+=''.join(f'gate!(g{i:02d},{i});\n' for i in range(60))
inputs=json.loads((E.parent/'slice-d-finish-20261105/NGM_NATIVE_INPUTS.json').read_text())
inputs[C+'NHI_tensor.rs']=code
inputs[C+'weights.rs']+='\n#[cfg(kani)] #[path="NHI_tensor.rs"] mod NHI_tensor;\n'
patch=[]
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True)
 patch+=difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if not r.returncode else '/dev/null',tofile='b/'+n)
(E/'NHI_harness.patch').write_text(''.join(patch))
(E/'NHI_NATIVE_PLAN.json').write_text(json.dumps(dict(family='tensor one-window local records',groups=60,attempts=120,domain='n in {1,4,16}; j<n; 64 mutable QM31 cells; arbitrary raw words; canonicality restricted only when applying Lean multiplication laws',products='opaque call-log, never native multiplication; log reply unconstrained for caller-control observations',property_groups={'0..15':'four written product cells, one limb each','16..31':'each SAME original x receiver limb','32..47':'each SAME selected row operand limb','48..51':'untouched arbitrary cell frame, each limb','52':'four source ordered opaque calls','53':'distinct write slots','54':'last product uses pre-write x','55':'all addressed slots in bounds','56':'reverse iterator initial cell','57':'outer width multiply by four','58':'S2 dimension/width sequence','59':'disjoint reverse-window earlier source cells'},frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'),indent=2)+'\n')
