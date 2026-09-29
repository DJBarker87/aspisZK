#[path="r91_reference/field.rs"] mod reference;
#[path="r81_canonical_basis.rs"] mod private;
use aspis_core::field::{QM31,CM31,M31,P};
fn k(x:[u32;4])->QM31 {QM31{c0:CM31::new(M31(x[0]),M31(x[1])),c1:CM31::new(M31(x[2]),M31(x[3]))}}
fn old(x:[u32;4])->reference::QM31 {reference::QM31{c0:reference::CM31::new(reference::M31(x[0]),reference::M31(x[1])),c1:reference::CM31::new(reference::M31(x[2]),reference::M31(x[3]))}}
fn limbs(x:QM31)->[u32;4] {[x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0]}
fn main(){
    let mut rng=0x94ff_2d90_0c31_aa54u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(P))as u32};
    let boundary=[0,1,P/2,P-1];
    for case in 0..262144usize {
        let z:[u32;8]=core::array::from_fn(|j|if case<65536{boundary[(case>>(2*j))&3]}else{next()});
        let x:[u32;4]=z[..4].try_into().unwrap();let y:[u32;4]=z[4..].try_into().unwrap();
        let [a,b,c,d,e,f,g,h]=z.map(i128::from);
        let expected=[a*e-b*f+2*(c*g-d*h)-(c*h+d*g),a*f+b*e+(c*g-d*h)+2*(c*h+d*g),
          a*g-b*h+c*e-d*f,a*h+b*g+c*f+d*e].map(|v|v.rem_euclid(i128::from(P))as u32);
        let v=old(x).mul(old(y));assert_eq!([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0],expected);
        assert_eq!(limbs(k(x).mul(k(y))),expected);
        assert_eq!(private::Q::from_limbs(x).unwrap().mul(private::Q::from_limbs(y).unwrap()).limbs(),expected);
        assert_eq!(limbs(aspis_core::field::r25_checked_dot(&[k(x)],&[k(y)]).unwrap()),expected);
        // Check the unreduced pair products/subtractions as integers, not
        // merely their residues: no wrapping can hide an intermediate error.
        let max=u128::from(u64::MAX);let [a,b,c,d,e,f,g,h]=z.map(u128::from);
        for (u,v,w,t) in [(a,b,e,f),(c,d,g,h),(a,b,g,h),(c,d,e,f)] {
            let product=(u+v)*(w+t);assert!(product<=max);
            assert_eq!(product.checked_sub(u*w).unwrap().checked_sub(v*t).unwrap(),u*t+v*w);
        }
    }
    for n in [0,1,4,17,19,271,4096] {
        let mut acc=private::Dot::new();let mut expected=k([0;4]);
        for _ in 0..n {let x=core::array::from_fn(|_|next());let y=core::array::from_fn(|_|next());
            acc.push(private::Q::from_limbs(x).unwrap(),private::Q::from_limbs(y).unwrap());
            let v=old(x).mul(old(y));expected=expected.add(k([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0]));}
        assert_eq!(acc.finish().limbs(),limbs(expected));
    }
    println!("R94_PRODUCT full_products=262144 corner_cases=65536 independent_i128=true checked_integer_pairs=true private_dot_lengths=7 max_dot_length=4096");
}
