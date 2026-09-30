// Same semantic polynomial and retained G basis, evaluated in one private
// canonical region. Every sent coefficient is checked, even at x=0 or x=1.
fn r107_in(v:K)->Option<r81_canonical::Q> {
    r81_canonical::Q::from_limbs([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0])
}
fn r107_out(q:r81_canonical::Q)->K {
    let [a,b,c,d]=q.limbs();K{c0:aspis_core::field::CM31::new(M31(a),M31(b)),c1:aspis_core::field::CM31::new(M31(c),M31(d))}
}
#[inline(never)]
fn r107_try_round(claim:K,sent:&[K;27],x:K,basis:&mut[K;27])->Option<K> {
    use r81_canonical::{Q,Dot};
    let x=r107_in(x)?;let claim=r107_in(claim)?;
    let mut powers=[Q::ZERO;27];powers[0]=x;
    let mut dot=Dot::new();dot.push(claim,x);
    let first=Q::ONE.sub(x.add(x));dot.push(r107_in(sent[0])?,first);basis[0]=r107_out(first);
    for degree in 2..=27 {
        let power=if degree%2==0 {powers[degree/2-1].square()}else{powers[degree-2].mul(x)};
        powers[degree-1]=power;
        let value=power.sub(x);dot.push(r107_in(sent[degree-1])?,value);
        basis[degree-1]=r107_out(value);
    }
    Some(r107_out(dot.finish()))
}
#[inline(never)]
pub fn evaluate_round(claim:K,sent:&[K;27],x:K,basis:&mut[K;27])->K {
    r107_try_round(claim,sent,x,basis)
        .unwrap_or_else(||r107_retained_round(claim,sent,x,basis))
}
#[cfg(not(target_os="solana"))]
pub fn r107_controls() {
    let mut rng=0x107ab_9723_fe4451u64;
    fn sample(r:&mut u64)->K {
        let mut m=||{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(P))as u32)};
        K{c0:aspis_core::field::CM31::new(m(),m()),c1:aspis_core::field::CM31::new(m(),m())}
    }
    for case in 0..8192 {
        let mut next=||if case==0{K::ZERO}else if case==1{all_max()}else{sample(&mut rng)};
        let sent=core::array::from_fn(|_|next());let claim=next();
        let x=match case%4{0=>K::ZERO,1=>K::ONE,2=>K::ONE.neg(),_=>next()};
        let mut old=[K::ZERO;27];let mut new=[K::ONE;27];
        let expected=r107_retained_round(claim,&sent,x,&mut old);
        assert_eq!(r107_try_round(claim,&sent,x,&mut new),Some(expected));assert_eq!(old,new);
        assert_eq!(evaluate_round(claim,&sent,x,&mut new),horner_round(claim,&sent,x));assert_eq!(old,new);
    }
    let hook=std::panic::take_hook();std::panic::set_hook(Box::new(|_|{}));let mut malformed=0;
    for position in 0..29 {for limb in 0..4 {for bad in [P,P+1,u32::MAX] {for x in [K::ZERO,K::ONE,all_max()] {
        let mut raw=[M31::ZERO;4];raw[limb]=M31(bad);
        let v=K{c0:aspis_core::field::CM31::new(raw[0],raw[1]),c1:aspis_core::field::CM31::new(raw[2],raw[3])};
        let mut sent=[K::ONE;27];let mut claim=K::ONE;let mut x=x;
        if position<27{sent[position]=v;}else if position==27{claim=v;}else{x=v;}
        let mut b=[K::ZERO;27];assert_eq!(r107_try_round(claim,&sent,x,&mut b),None);
        let new=std::panic::catch_unwind(||{let mut b=[K::ZERO;27];let y=evaluate_round(claim,&sent,x,&mut b);(y,b)});
        let old=std::panic::catch_unwind(||{let mut b=[K::ZERO;27];let y=r107_retained_round(claim,&sent,x,&mut b);(y,b)});
        match(new,old){(Ok(a),Ok(b))=>assert_eq!(a,b),(Err(_),Err(_))=>(),_=>panic!("raw semantic behavior changed")};malformed+=1;
    }}}}
    std::panic::set_hook(hook);
    println!("R107_SEMANTIC rounds=8192 basis_coordinates=221184 raw_boundary_cases={malformed} zero_one_validation=true retained_horner=true");
}
