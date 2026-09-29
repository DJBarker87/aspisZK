// Actual new public kernel versus frozen R55 field and independent u128 model.
#[path="r56_reference/field.rs"] mod reference;
use aspis_core::field::{QM31 as K,CM31,M31,P,PreparedQm31Multiplier};
fn encode(k:K)->[u8;16]{let mut b=[0;16];k.write_le_bytes(&mut b);b}
fn mk(v:&[u32])->K{K{c0:CM31::new(M31(v[0]),M31(v[1])),c1:CM31::new(M31(v[2]),M31(v[3]))}}
fn old(v:&[u32])->reference::QM31{reference::QM31{
    c0:reference::CM31::new(reference::M31(v[0]),reference::M31(v[1])),
    c1:reference::CM31::new(reference::M31(v[2]),reference::M31(v[3]))}}
fn old_bytes(v:reference::QM31)->[u8;16]{let mut b=[0;16];v.write_le_bytes(&mut b);b}
fn independent(x:&[u32;8])->K{
    let [a,b,c,d,e,f,g,h]=x.map(u128::from);let p=u128::from(P);let pp=p*p;
    let v=[a*e+2*c*g+4*pp-b*f-2*d*h-c*h-d*g,
           a*f+b*e+c*g+2*c*h+2*d*g+pp-d*h,
           a*g+c*e+2*pp-b*h-d*f,a*h+b*g+c*f+d*e];
    mk(&v.map(|v|(v%p)as u32))
}
fn main(){
    let mut seed=0x56fa_1823_994a_7561u64;
    let mut next=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;(seed%u64::from(P))as u32};
    let mut cases=0;
    for case in 0..265536 {
        let mut l=core::array::from_fn::<_,8,_>(|_|next());
        if case<65536 {let values=[0,1,P-2,P-1];let mut k=case;for x in &mut l{*x=values[k%4];k/=4;}}
        let a=mk(&l[..4]);let b=mk(&l[4..]);let expected=independent(&l);
        assert_eq!(a.mul(b),expected);
        assert_eq!(encode(expected),old_bytes(old(&l[..4]).mul(old(&l[4..]))));
        assert_eq!(PreparedQm31Multiplier::new(a).mul(b),expected);
        assert_eq!(aspis_core::field::r25_checked_dot(&[a],&[b]),Some(expected));
        cases+=1;
    }
    // All guards must still reject raw constructors; preserve the exact old
    // public fallback outcome, including panics, without manufacturing validity.
    let hook=std::panic::take_hook();std::panic::set_hook(Box::new(|_|{}));
    let mut invalid=0;
    for limb in 0..8 {for bad in [P,P+1,u32::MAX] {let mut l=[1;8];l[limb]=bad;
        let actual=std::panic::catch_unwind(||encode(mk(&l[..4]).mul(mk(&l[4..]))));
        let expected=std::panic::catch_unwind(||old_bytes(old(&l[..4]).mul(old(&l[4..]))));
        match(actual,expected){(Ok(a),Ok(b))=>assert_eq!(a,b),(Err(_),Err(_))=>(),_=>panic!("fallback changed")}
        assert_eq!(aspis_core::field::r25_checked_dot(&[mk(&l[..4])],&[mk(&l[4..])]),None);invalid+=1;
    }}
    std::panic::set_hook(hook);
    println!("R56_PRODUCT canonical_pairs={cases} boundary_pairs=65536 random_pairs=200000 frozen_source=true independent_u128=true prepared_and_checked_dot=true invalid_constructor_cases={invalid} fallback_retained=true");
}
