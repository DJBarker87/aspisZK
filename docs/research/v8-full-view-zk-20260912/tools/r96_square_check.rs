use aspis_core::field::{M31,CM31,QM31 as K,P};
#[path="r81_canonical_basis.rs"]mod private;
include!("r96_raw_square.rs");
fn main(){
    let p=u128::from(P);let mut seed=0x967319bcca083d0fu64;
    for case in 0..262144 {
        let x:[u32;4]=core::array::from_fn(|i|if case<256{[0,1,P/2,P-1][(case>>(2*i))&3]}else{
            seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;(seed%u64::from(P))as u32});
        let [a,b,c,d]=x.map(u128::from);let partial=|v:u128|(v&p)+(v>>31);
        let ab=(a+b)*(a+p-b);let u=partial((c+d)*(c+p-d));let v=partial(2*c*d);
        assert!(u<5*p && v<3*p);
        let cross=((a+b)*(c+d)).checked_sub(a*c).unwrap().checked_sub(b*d).unwrap();
        assert_eq!(cross,a*d+b*c);
        let raws=[(ab+2*u+3*p).checked_sub(v).unwrap(),2*a*b+u+2*v,2*(a*c+p*p-b*d),2*cross];
        for r in raws{assert!(r<=u128::from(u64::MAX));}
        assert_eq!(r96_raw_square(x).map(u128::from),raws);
        let expected=raws.map(|r|(r%p)as u32);
        let [a,b,c,d]=x.map(i128::from);let pp=i128::from(P);
        assert_eq!(expected,[a*a-b*b+2*(c*c-d*d)-2*c*d,2*a*b+c*c-d*d+4*c*d,2*(a*c-b*d),2*(a*d+b*c)].map(|r|r.rem_euclid(pp)as u32));
        let value=K{c0:CM31::new(M31(x[0]),M31(x[1])),c1:CM31::new(M31(x[2]),M31(x[3]))};
        let actual=value.square();assert_eq!([actual.c0.a.0,actual.c0.b.0,actual.c1.a.0,actual.c1.b.0],expected);
        assert_eq!(private::Q::from_limbs(x).unwrap().square().limbs(),expected);
    }
    println!("R96_SQUARE cases=262144 corner_cases=256 independent_i128=true raw_integer_no_wrap=true private_and_generic=true");
}
