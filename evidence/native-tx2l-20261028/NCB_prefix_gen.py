from NCB_generate import *
p='crates/aspis-r1-cost-probe/src/verifier.rs'
body='''let value=flat[index];
        prefixes.push(product);
        product=product.mul(value);
        index+=1;'''
src=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True);assert body in src
text=r'''
#[cfg(kani)] mod NCB_prefix {
 use super::*;
 static mut LEFT:u32=0;static mut RIGHT:u32=0;static mut RESULT:u32=0;static mut CALLS:u8=0;
 fn mul(a:M31,b:M31)->M31 {unsafe{
  assert!(CALLS==0);CALLS=1;assert!(a.0==LEFT&&b.0==RIGHT);
  let result:u32=kani::any();kani::assume(u64::from(result)==(u64::from(a.0)*u64::from(b.0))%2147483647);
  RESULT=result;M31(result)
 }}
 #[kani::proof] #[kani::unwind(64)] ATTR
 fn copy_negative(){let a=[0u32,0,0,0,0,0,0,1,0,0,0,0,0,0,0,512];let mut b=[0u32;16];b.copy_from_slice(&a);assert!(b[15]==0);}
'''.replace('ATTR',attrs)
for label,check in [('control','assert!(index==before+1);unsafe{assert!(CALLS==1&&product.0==RESULT);}'),('length','assert!(prefixes.len()==before+1);assert!(prefixes.as_ptr()==ptr);'),('new','assert!(prefixes[before].0==initial);'),('frame','let j:usize=kani::any();kani::assume(j<before);assert!(prefixes[j].0==old[j]);')]:
 text+='\n#[kani::proof] #[kani::unwind(512)]\n'+attrs+'#[kani::stub(M31::mul,mul)]\nfn '+label+'(){\n'
 text+='''let old:[u32;110]=kani::any();let input:[u32;110]=kani::any();let flat=input.map(M31);
 let mut index:usize=kani::any();kani::assume(index<110);let before=index;
 let mut prefixes:Vec<M31>=old.map(M31).into();prefixes.truncate(index);let ptr=prefixes.as_ptr();
 let mut product=M31(kani::any());let initial=product.0;
 unsafe{LEFT=product.0;RIGHT=flat[index].0;CALLS=0;}
 '''+body+'\n'+check+'\n}\n'
text+='}\n';emit(p,text,'NCB_prefix')
(E/'NCB_PREFIX_SOURCE.json').write_text(__import__('json').dumps({'source':p,'revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','body':body,'sha256':hashlib.sha256(body.encode()).hexdigest(),'domain':'arbitrary index<110, prefix len=index/capacity110, arbitrary words; one source iteration only','stub_theorem':'AspisR1.LPf_BaseMultiply.source; all u32 operands'},indent=2)+'\n')
