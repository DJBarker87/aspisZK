from pathlib import Path
import json,sys
EVD=Path(__file__).resolve().parent
sys.path.insert(0,str(EVD));from NEA_payload import save
s='''use super::*;
#[path="NEA_fold_reference.rs"] mod NEA_fold_reference;
use NEA_fold_reference::{NEA_Ops,circle_ref,line_ref};
const P:u32=2147483647;
fn canon(x:E)->bool {let w=x.to_limbs();w[0]<P&&w[1]<P&&w[2]<P&&w[3]<P&&w[4]<P&&w[5]<P&&w[6]<P&&w[7]<P}
fn any_e()->E {let w:[u32;8]=kani::any();kani::assume(w[0]<P&&w[1]<P&&w[2]<P&&w[3]<P&&w[4]<P&&w[5]<P&&w[6]<P&&w[7]<P);E::from_limbs(w).unwrap()}
pub fn domain(alpha:E,a:[E;4],i:&[M31;5],line:bool)->bool {canon(alpha)&&canon(a[0])&&canon(a[1])&&canon(a[2])&&canon(a[3])&&if line{i[2].0<P&&i[3].0<P&&i[4].0<P}else{i[0].0<P&&i[1].0<P}}
'''
for name,left,right,out,zeroL,zeroR,zeroO,count in [('EM','E','E','E','E::ZERO','E::ZERO','E::ZERO',8),('SM','E','M31','E','E::ZERO','M31::ZERO','E::ZERO',16),('BM','M31','M31','M31','M31::ZERO','M31::ZERO','M31::ZERO',8)]:
 entry=name+'Entry';memo=name+'Memo'
 s+=f'''#[derive(Clone,Copy)] pub(super) struct {entry} {{x:{left},y:{right},out:{out}}}
pub(super) struct {memo} {{count:usize,slots:[{entry};{count}]}}
pub(super) static mut {name}:{memo}={memo}{{count:0,slots:[{entry}{{x:{zeroL},y:{zeroR},out:{zeroO}}};{count}]}};
'''
 fn={'EM':'em','SM':'sm','BM':'bm'}[name]
 predX='canon(x)' if left=='E' else 'x.0<P';predY='canon(y)' if right=='E' else 'y.0<P'
 for replay in [False,True]:
  f=fn+('_replay' if replay else '')
  s+=f'fn {f}(x:{left},y:{right})->{out} {{assert!({predX}&&{predY});unsafe {{\n'
  for k in range(count):s+=f'if {name}.count>{k} && {name}.slots[{k}].x==x && {name}.slots[{k}].y==y {{return {name}.slots[{k}].out;}}\n'
  if replay:s+='panic!("reference operand has no matching native call");\n'
  else:
   s+= 'let out=any_e();\n' if out=='E' else 'let w:u32=kani::any();kani::assume(w<P);let out=M31(w);\n'
   s+=f'assert!({name}.count<{count});let k={name}.count;{name}.slots[k]={entry}{{x,y,out}};{name}.count+=1;out\n'
  s+='}}\n'
s+='''pub(super) unsafe fn reset(){EM.count=0;SM.count=0;BM.count=0;}
struct Replay;
impl NEA_Ops<E,M31> for Replay {
 fn add(x:E,y:E)->E {assert!(canon(x)&&canon(y));x.add(y)}
 fn sub(x:E,y:E)->E {assert!(canon(x)&&canon(y));x.sub(y)}
 fn mul(x:E,y:E)->E {em_replay(x,y)}
 fn scale(x:E,y:M31)->E {sm_replay(x,y)}
 fn base_mul(x:M31,y:M31)->M31 {bm_replay(x,y)}
}
pub fn circle_post(r:E,alpha:E,a:[E;4],inverse:&[M31;5])->bool {let expected=circle_ref::<E,M31,Replay>(alpha,a,*inverse,QUARTER);if cfg!(NEA_wrong_fold){r!=expected}else{r==expected}}
pub fn line_post(r:E,alpha:E,a:[E;4],inverse:&[M31;5])->bool {let expected=line_ref::<E,M31,Replay>(alpha,a,*inverse,QUARTER,M31(1073741824));if cfg!(NEA_wrong_fold){r!=expected}else{r==expected}}
'''
for fn,target in [('circle','circle_fold_with_inverses'),('line','line_fold_with_inverses')]:
 s+=f'''#[cfg_attr(NEA_fold,kani::proof_for_contract({target}))]
#[cfg_attr(not(NEA_fold),kani::proof)]
#[kani::stub(E::mul,em)]
#[kani::stub(E::mul_m31,sm)]
#[kani::stub(M31::mul,bm)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEA_copy::KMX_copy_nonoverlapping)]
fn {fn}() {{let alpha=any_e();let a=[any_e(),any_e(),any_e(),any_e()];let inverse=[M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any()),M31(kani::any())];kani::assume(domain(alpha,a,&inverse,{str(fn=='line').lower()}));let _={target}(alpha,a,&inverse);}}
'''
(EVD/'NEA_fold.rs.txt').write_text(s)
x=json.loads((EVD/'NEA_PAYLOAD.json').read_text());p='crates/aspis-r1-cost-probe/src/verifier.rs';v=x[p]
for fn,line in [('circle_fold_with_inverses',False),('line_fold_with_inverses',True)]:
 v=v.replace(f'fn {fn}(alpha:',f'''#[cfg_attr(all(kani,NEA_fold),kani::requires(NEA_fold::domain(alpha,a,inverse,{str(line).lower()})))]
#[cfg_attr(all(kani,NEA_fold),kani::modifies(&raw mut NEA_fold::EM,&raw mut NEA_fold::SM,&raw mut NEA_fold::BM))]
#[cfg_attr(all(kani,NEA_fold),kani::ensures(|r| NEA_fold::{'line' if line else 'circle'}_post(*r,alpha,a,inverse)))]
fn {fn}(alpha:''')
 v=v.replace(f'fn {fn}(alpha:E,a:[E;4],inverse:&[M31;5])->E {{',f'fn {fn}(alpha:E,a:[E;4],inverse:&[M31;5])->E {{\n    #[cfg(all(kani,NEA_fold))] unsafe {{NEA_fold::reset();}}')
v+='\n#[cfg(kani)] #[path="NEA_fold.rs"] mod NEA_fold;\n';x[p]=v
x['crates/aspis-r1-cost-probe/src/NEA_fold.rs']=s
x['crates/aspis-r1-cost-probe/src/NEA_fold_reference.rs']=(EVD/'NEA_fold_reference.rs.txt').read_text().replace('#![no_std]\n','')
save(x)
