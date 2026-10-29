from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));from NEA_payload import save
s='''use super::*;
const P:u32=2147483647;
static mut INDEX:usize=0;static mut PRODUCT:M31=M31::ZERO;static mut FRAME:usize=0;static mut VALUE:M31=M31::ZERO;
static mut COUNT:usize=0;static mut X:M31=M31::ZERO;static mut Y:M31=M31::ZERO;static mut OUT:M31=M31::ZERO;
pub(super) fn seed(flat:&[M31])->(Vec<M31>,M31,usize){
 let index:usize=kani::any();kani::assume(index<flat.len());
 let words:[M31;110]=kani::any();let prefixes=words[..index].to_vec();
 let product=M31(kani::any());let frame:usize=kani::any();kani::assume(index==0||frame<index);
 unsafe{INDEX=index;PRODUCT=product;FRAME=frame;if index>0{VALUE=prefixes[frame];}COUNT=0;}
 (prefixes,product,index)
}
fn mul(x:M31,y:M31)->M31 {let r:u32=kani::any();kani::assume(r<P);unsafe{COUNT+=1;X=x;Y=y;OUT=M31(r);}M31(r)}
pub(super) fn observe(flat:&[M31],prefixes:&[M31],product:M31,index:usize){unsafe{
 assert!(COUNT==1&&X==PRODUCT&&Y==flat[INDEX]&&product==OUT);
 assert!(index==INDEX+1&&prefixes.len()==index&&prefixes[INDEX]==PRODUCT);
 if INDEX>0 {assert!(prefixes[FRAME]==VALUE);}
 if cfg!(NEA_wrong_prefix){assert!(prefixes.len()==INDEX);}
}}
#[kani::proof]
#[kani::unwind(120)]
#[kani::stub(M31::mul,mul)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NEA_copy::KMX_copy_nonoverlapping)]
fn step(){let flat:[M31;110]=kani::any();let _=batch_prefix_products(&flat);}
'''
p=json.loads((E/'NEA_PAYLOAD.json').read_text());v=p['crates/aspis-r1-cost-probe/src/verifier.rs']
v=v.replace('    while index<flat.len() {\n        let value=flat[index];','    #[cfg(all(kani,NEA_prefix))] { (prefixes,product,index)=NEA_prefix::seed(flat); }\n    while index<flat.len() {\n        let value=flat[index];',1)
v=v.replace('        product=product.mul(value);\n        index+=1;','        product=product.mul(value);\n        index+=1;\n        #[cfg(all(kani,NEA_prefix))] {NEA_prefix::observe(flat,&prefixes,product,index);break;}',1)
v+='\n#[cfg(all(kani,NEA_prefix))] #[path="NEA_prefix.rs"] mod NEA_prefix;\n'
p['crates/aspis-r1-cost-probe/src/verifier.rs']=v;p['crates/aspis-r1-cost-probe/src/NEA_prefix.rs']=s
(E/'NEA_prefix.rs.txt').write_text(s);save(p)
