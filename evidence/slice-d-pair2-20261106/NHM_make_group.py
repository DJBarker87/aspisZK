from pathlib import Path
import subprocess,difflib,json
E=Path(__file__).resolve().parent;C='crates/aspis-r1-cost-probe/src/'
code=r'''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
struct Log{left:[[u32;8];2],right:[[u32;8];2],reply:[[u32;8];2],calls:usize}
fn op(x:[u32;8],y:[u32;8],l:&mut Log)->[u32;8]{let i=l.calls;l.left[i]=x;l.right[i]=y;l.calls+=1;l.reply[i]}
fn coefficient(coeff:&mut [[u32;8];12],j:usize,field:[u32;8],l:&mut Log){let group=S2_INACTIVE_GROUPS[j]as usize;coeff[group]=op(coeff[group],field,l);}
fn weight(low:&[[u32;8];16],group:usize,bit:usize,before:[u32;8],l:&mut Log)->[u32;8]{let challenge=low[bit];if S2_INACTIVE_MASKS[group]&(1<<bit)!=0{op(before,challenge,l)}else{before}}
fn accumulate(coeff:&[[u32;8];12],group:usize,weight:[u32;8],before:[u32;8],l:&mut Log)->[u32;8]{let product=op(coeff[group],weight,l);op(before,product,l)}
fn exercise(family:usize,g:usize){
 let before:[[u32;8];12]=kani::any();let mut low:[[u32;8];16]=kani::any();let low_before=low;let a:[u32;8]=kani::any();let b:[u32;8]=kani::any();let replies:[[u32;8];2]=kani::any();
 let j:usize=kani::any();kani::assume(j<64);let group:usize=kani::any();kani::assume(group<12);let bit:usize=kani::any();kani::assume(bit<16);let k:usize=kani::any();kani::assume(k<12);
 let mut coeff=before;let mut l=Log{left:[[0;8];2],right:[[0;8];2],reply:replies,calls:0};
 let mut target=S2_INACTIVE_GROUPS[j]as usize;let mut mask=S2_INACTIVE_MASKS[group]&(1<<bit)!=0;
 let mut result=if family==0{coefficient(&mut coeff,j,a,&mut l);a}else if family==1{weight(&low,group,bit,a,&mut l)}else{accumulate(&coeff,group,b,a,&mut l)};
 if cfg!(NHM_invert){
  if family==0{match g{0=>target=12,1=>l.left[0][0]^=1,2=>l.right[0][0]^=1,3=>coeff[target][0]^=1,_=>coeff[k][0]^=1}}
  else if family==1{match g{0=>l.calls^=1,1=>l.left[0][0]^=1,2=>l.right[0][0]^=1,3=>result[0]^=1,_=>low[k][0]^=1}}
  else{match g{0=>l.left[0][0]^=1,1=>l.left[1][0]^=1,2=>l.right[1][0]^=1,_=>result[0]^=1}}
 }
 if cfg!(NHM_mask_wrong){mask=!mask;}
 let good=if family==0{match g{0=>target<12,1=>l.left[0]==before[target],2=>l.right[0]==a,3=>coeff[target]==replies[0]&&l.calls==1,_=>if k!=target{coeff[k]==before[k]}else{true}}}
 else if family==1{match g{0=>l.calls==if mask{1}else{0},1=>if mask{l.left[0]==a}else{true},2=>if mask{l.right[0]==low[bit]}else{true},3=>result==if mask{replies[0]}else{a},_=>low==low_before}}
 else{match g{0=>l.left[0]==before[group]&&l.right[0]==b,1=>l.left[1]==a,2=>l.right[1]==replies[0]&&result==replies[1]&&l.calls==2&&coeff==before,3=>result==replies[1]&&l.calls==2&&coeff==before,_=>coeff==before}};
 assert!(good);
}
fn control(family:usize){
 let n=if family==0{16}else if family==1{4}else{64};let stop:usize=kani::any();kani::assume(stop<=n);let s:usize=kani::any();kani::assume(s<4);
 let mut log=[0usize;64];let mut calls=0;let mut rejected=false;
 for j in 0..n{log[calls]=if family==0{16*s+j}else{j};calls+=1;if j==stop{rejected=true;break;}}
 let k:usize=kani::any();kani::assume(k<calls);
 if cfg!(NHM_invert){log[k]^=1;}
 let good=calls==if stop<n{stop+1}else{n}&&rejected==(stop<n)&&log[k]==if family==0{16*s+k}else{k};
 assert!(good);
}
macro_rules! gate{($name:ident,$family:expr,$g:expr)=>{#[kani::proof]#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){exercise($family,$g)}};}
macro_rules! ctrl{($name:ident,$family:expr)=>{#[kani::proof]#[kani::unwind(66)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn $name(){control($family)}};}
'''
for fam,name in [(0,'coefficient'),(1,'weight'),(2,'accumulate')]:
 for g in range(5):
  if (fam==1 and g==4)or(fam==2 and g>=2):
   bound=514 if fam==1 else 386
   code+=f'#[kani::proof]#[kani::unwind({bound})]#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]fn {name}{g:02}(){{exercise({fam},{g})}}\n'
  else:code+=f'gate!({name}{g:02},{fam},{g});\n'

for fam in range(3):code+=f'ctrl!(control{fam:02},{fam});\n'
inputs=json.loads((E.parent/'slice-d-finish-20261105/NGM_NATIVE_INPUTS.json').read_text());inputs[C+'NHM_group.rs']=code;inputs[C+'weights.rs']+='\n#[cfg(kani)] #[path="NHM_group.rs"] mod NHM_group;\n'
patch=''
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True)
 patch+=''.join(difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n))
(E/'NHM_group.patch').write_text(patch)
