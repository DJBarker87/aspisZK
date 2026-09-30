#[path="r81_canonical_basis.rs"] mod r109_private;
use r109_private::Q as Q109;
fn r109_in(v:K)->Option<Q109>{Q109::from_limbs([v.c0.a.0,v.c0.b.0,v.c1.a.0,v.c1.b.0])}
fn r109_out(v:Q109)->K{let [a,b,c,d]=v.limbs();K{c0:corelib::field::CM31::new(M31(a),M31(b)),c1:corelib::field::CM31::new(M31(c),M31(d))}}
fn r109_convert<const N:usize>(v:[K;N])->Option<[Q109;N]>{let mut q=[Q109::ZERO;N];for i in 0..N{q[i]=r109_in(v[i])?;}Some(q)}
fn r109_basis(a:Q109,b:Q109)->[Q109;16]{
    let a2=a.square();let b2=b.square();
    let ap=[Q109::ONE,a2.mul(a),a2,a];let bp=[Q109::ONE,b2.mul(b),b2,b];
    core::array::from_fn(|j|if j<4{ap[j]}else if j%4==0{bp[j/4]}else{ap[j%4].mul(bp[j/4])})
}
#[inline(never)]
fn r109_try_geometry(abc:[K;3],alpha:[K;4])->Option<([K;16],[K;3],[K;16])>{
    let [a,b,c]=r109_convert(abc)?;let alpha=r109_convert(alpha)?;
    let low=r109_basis(alpha[0],alpha[1]);let high=r109_basis(alpha[2],alpha[3]);
    let mut xn=[Q109::ZERO;16];let mut xc=[Q109::ZERO;2];
    let mut yn=[Q109::ZERO;16];let mut yc=[Q109::ZERO;3];
    for input in 0..16 {
        let y=input&1;let j=input>>1;let mut row=j;let mut bit=0;
        let mut value=low[input];
        while row&(1<<bit)!=0 {
            row^=1<<bit;bit+=1;value=value.half();
            xn[2*row+y]=xn[2*row+y].add(value);
        }
        row|=1<<bit;
        if row<8 {xn[2*row+y]=xn[2*row+y].add(value);}else{xc[y]=xc[y].add(value);}
        if y==0 {yn[input+1]=yn[input+1].add(low[input]);}
        else {
            yn[input-1]=yn[input-1].add(low[input].half());
            let mut row=j>>1;let mut bit=0;let mut value=low[input].half();
            while row&(1<<bit)!=0 {
                row^=1<<bit;bit+=1;value=value.half();let dest=2*((row<<1)|(j&1));
                yn[dest]=yn[dest].sub(value);
            }
            row|=1<<bit;let line=(row<<1)|(j&1);let dest=2*(line%8);
            if line<8 {yn[dest]=yn[dest].sub(value);}else{yc[dest]=yc[dest].sub(value);}
        }
    }
    let normal=core::array::from_fn(|i|r109_out(Q109::dot([a,b,c],[low[i],xn[i],yn[i]])));
    let carry=[Q109::dot([b,c],[xc[0],yc[0]]),b.mul(xc[1]),c.mul(yc[2])].map(r109_out);
    Some((normal,carry,high.map(r109_out)))
}
#[inline(never)]
fn geometry(abc:[K;3],alpha:[K;4])->([K;16],[K;3],[K;16]){
    r109_try_geometry(abc,alpha).unwrap_or_else(||r109_retained_geometry(abc,alpha))
}
#[cfg(not(target_os="solana"))]
pub(super) fn r109_controls(){
    use corelib::field::{P,CM31};let mut rng=0x109ba_63991fe01u64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;M31((rng%u64::from(P))as u32)};
    for case in 0..8192 {
        let all:[K;7]=core::array::from_fn(|i|{
            let mut m=||if case==0{M31::ZERO}else if case==1{M31(P-1)}else{next()};
            let q=K{c0:CM31::new(m(),m()),c1:CM31::new(m(),m())};
            if (2..30).contains(&case){let mut raw=[M31::ZERO;4];if i==(case-2)/4{raw[(case-2)%4]=M31(P-1);}
                K{c0:CM31::new(raw[0],raw[1]),c1:CM31::new(raw[2],raw[3])}}
            else if case==30{K::ONE}else{q}
        });
        let abc=all[..3].try_into().unwrap();let alpha=all[3..].try_into().unwrap();
        let expected=r109_retained_geometry(abc,alpha);
        assert_eq!(r109_try_geometry(abc,alpha),Some(expected));assert_eq!(geometry(abc,alpha),expected);
    }
    let hook=std::panic::take_hook();std::panic::set_hook(Box::new(|_|{}));let mut malformed=0;
    for at in 0..7{for limb in 0..4{for bad in [P,P+1,u32::MAX]{
        let mut all=[K::ONE;7];let mut raw=[M31::ZERO;4];raw[limb]=M31(bad);
        all[at]=K{c0:CM31::new(raw[0],raw[1]),c1:CM31::new(raw[2],raw[3])};
        let abc=all[..3].try_into().unwrap();let alpha=all[3..].try_into().unwrap();
        assert_eq!(r109_try_geometry(abc,alpha),None);
        match(std::panic::catch_unwind(||geometry(abc,alpha)),std::panic::catch_unwind(||r109_retained_geometry(abc,alpha))){
            (Ok(a),Ok(b))=>assert_eq!(a,b),(Err(_),Err(_))=>(),_=>panic!("raw geometry boundary changed")
        }malformed+=1;
    }}}
    std::panic::set_hook(hook);
    println!("R109_GEOMETRY profiles=8192 scalar_coordinates=286720 malformed={malformed} carry_zero_extension_retained=true");
}
