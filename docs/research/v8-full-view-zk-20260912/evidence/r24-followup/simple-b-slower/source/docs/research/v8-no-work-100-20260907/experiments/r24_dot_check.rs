#[path="r20_private_dot_adapter.rs"] mod actual;
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
