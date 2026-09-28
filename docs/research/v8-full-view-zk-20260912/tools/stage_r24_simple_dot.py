#!/usr/bin/env python3
"""Rebenchmark whole-dot against newly cheap scalar multiplication."""
import argparse,hashlib,json,shutil
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();src=a.control;dst=a.output
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((src/'r18-stage.json').read_text());assert len(m['files'])==176 and 'r24_prepared' in m
for n,h in m['files'].items():assert sha(src/n)==h,n
assert not dst.exists();dst.mkdir()
for n in ['crates','docs','programs','xtask','audit']:shutil.copytree(src/n,dst/n,ignore=shutil.ignore_patterns('target','.git','*-keypair.json'))
for n in ['Cargo.toml','Cargo.lock','r17-stage.json','r17-sbf-probe.json','r19_canonical_check.rs',*m['files']]:
    if not(dst/n).exists():(dst/n).parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src/n,dst/n)
ex=dst/'docs/research/v8-no-work-100-20260907/experiments';adapter=ex/'r20_private_dot_adapter.rs';reference=ex/'r24_reference_dot_adapter.rs';shutil.copy2(adapter,reference)
adapter.write_text('''//! Exact checked dot using the new guarded scalar product, research candidate.
use aspis_core::field::{QM31 as K,P};
#[inline(never)]
pub(super) fn dot(left:&[K],right:&[K])->Option<K> {
    if left.len()!=right.len() || left.len()>4096 {return None;}
    let canonical=|v:&K|v.c0.a.0<P && v.c0.b.0<P && v.c1.a.0<P && v.c1.b.0<P;
    let mut total=K::ZERO;
    for(a,b)in left.iter().zip(right) {
        if !canonical(a)||!canonical(b){return None;}
        total=total.add(a.mul(*b));
    }
    Some(total)
}
''')
test=ex/'r24_dot_check.rs';test.write_text('''#[path="r20_private_dot_adapter.rs"] mod actual;
#[path="r24_reference_dot_adapter.rs"] mod original;
use aspis_core::field::{QM31 as K,CM31,M31,P};
fn main(){
    let mut seed=0x24ab56cdef789012u64;
    let mut sample=||{let mut x=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;M31(seed as u32%P)};K{c0:CM31::new(x(),x()),c1:CM31::new(x(),x())}};
    let lengths=[0,1,2,3,4,5,7,8,9,15,16,27,63,64,65,271,1024,4096];let mut cases=0;
    for n in lengths {for trial in 0..32 {
        let mut a:Vec<_>=(0..n).map(|_|sample()).collect();let mut b:Vec<_>=(0..n).map(|_|sample()).collect();
        if trial==0 {a.fill(K::ZERO);}if trial==1 {a.fill(K{c0:CM31::new(M31(P-1),M31(P-1)),c1:CM31::new(M31(P-1),M31(P-1))});b.clone_from(&a);}
        assert_eq!(actual::dot(&a,&b),original::dot(&a,&b));cases+=1;
    }}
    assert_eq!(actual::dot(&[K::ONE],&[]),None);assert_eq!(actual::dot(&vec![K::ZERO;4097],&vec![K::ZERO;4097]),None);
    let mut bad_cases=0;
    for n in [1,4,27,271] {for side in 0..2 {for pos in 0..n {for limb in 0..4 {for bad in [P,P+1,u32::MAX] {
        let mut a=vec![K::ONE;n];let mut b=a.clone();let target=if side==0{&mut a}else{&mut b};
        let value=&mut target[pos];match limb{0=>value.c0.a=M31(bad),1=>value.c0.b=M31(bad),2=>value.c1.a=M31(bad),_=>value.c1.b=M31(bad)};
        assert_eq!(actual::dot(&a,&b),None);assert_eq!(original::dot(&a,&b),None);bad_cases+=1;
    }}}}}
    println!("R24_DOT differential_cases={cases} noncanonical_cases={bad_cases} length_errors=2 max_terms=4096");
}
''')
cargo=ex/'performance-host/Cargo.toml';cargo.write_text(cargo.read_text()+'\n[[bin]]\nname = "r24-dot-check"\npath = "../r24_dot_check.rs"\n')
for path in [adapter,reference,test,cargo]:m['files'][str(path.relative_to(dst))]=sha(path)
m['r24_simple_dot']={'control_manifest_sha256':sha(src/'r18-stage.json'),'canonicality_retained':True,'max_terms':4096,'test_source_additions':2}
(dst/'r18-stage.json').write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'stage':str(dst),'pins':len(m['files'])}))
