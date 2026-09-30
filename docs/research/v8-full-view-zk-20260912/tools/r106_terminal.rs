// Included in r19_channel_ordinary. This candidate changes arithmetic only.
// The private geometry is derived here, never read from a prover cache.
#[inline(never)]
fn r106_geometry(high:&[CQ;16],finals:&[CQ;4],hb:&mut[CQ]) {
    assert_eq!(hb.len(),128);hb.fill(CQ::ZERO);
    for j in 0..64 {hb[j]=high[j&15].mul(finals[j>>4]);}
    for j in 0usize..64 {
        let mut value=hb[j];
        for bit in 0..j.trailing_ones() as usize {
            value=value.half();let row=j&!((1usize<<(bit+1))-1);
            hb[64+row]=hb[64+row].add(value);
        }
        if j+1<64 {hb[65+j]=hb[65+j].add(value);}
    }
}
#[inline(never)]
fn r106_sparse(coins:&[K],hb:&[CQ],normal:&[CQ;16],carry:&[CQ;3])->Option<CQ> {
    assert!(coins.len()>=271 && hb.len()==128);
    let mut result=r85_private::Dot::new();
    for low in 0..16 {
        let mut normal_sum=r85_private::Dot::new();
        let mut carry_sum=r85_private::Dot::new();
        let mut i=(11*low)%16;
        while i<271 {
            let coin=r85_in(coins[i])?;let group=(128+3*i)>>4;
            normal_sum.push(coin,hb[group]);
            if low<3 {carry_sum.push(coin,hb[64+group]);}
            i+=16;
        }
        result.push(normal[low],normal_sum.finish());
        if low<3 {result.push(carry[low],carry_sum.finish());}
    }
    result.finish().half_pow(8)
}
fn r106_low(normal:&[CQ;16],carry:&[CQ;3],values:&[CQ;19])->CQ {
    let mut dot=r85_private::Dot::new();
    for i in 0..16 {dot.push(normal[i],values[i]);}
    for i in 0..3 {dot.push(carry[i],values[16+i]);}
    dot.finish().half_pow(8).expect("fixed half exponent")
}
#[inline(never)]
fn r106_try_terminal(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,finals:&[K;4],
    kernel:&r17_weighted_groups::Kernel,coins:&[K])->Option<K> {
    let (normal,carry,high)=kernel.geometry_parts();
    let normal=r85_convert(*normal)?;let carry=r85_convert(*carry)?;
    let high=r85_convert(*high)?;let qfinals=r85_convert(*finals)?;
    let qbeta=r85_in(beta)?;let k=r85_in(audit[10])?;
    let mut hb=vec![CQ::ZERO;128];r106_geometry(&high,&qfinals,&mut hb);
    let mut entries=[K::ZERO;4];
    let plain=r85_in(r85_prepare(audit,abc,alpha,beta,finals,&mut entries)?)?;
    let entries=r85_convert(entries)?;
    let coordinates=[127usize,1023,126,1021].map(|row| {
        // All four low slots lie outside the three local carry slots.
        assert!(row&15>=3);
        normal[row&15].mul(hb[row>>4]).half_pow(8).expect("fixed half exponent")
    });
    let correction=CQ::dot([entries[1].sub(entries[0]),entries[3].sub(entries[2])],
        [coordinates[0].sub(coordinates[1]),coordinates[2].sub(coordinates[3])]);
    let inactive=r106_inactive(&hb);
    let ordinary=plain.add(correction).sub(entries[0].mul(r106_low(&normal,&carry,&inactive))).add(coordinates[1]);
    let sparse=r106_sparse(coins,&hb,&normal,&carry)?;
    Some(r85_out(ordinary.add(sparse.mul(qbeta.mul(k)))))
}
#[inline(never)]
pub(super) fn r106_terminal(audit:&[K;11],abc:[K;3],alpha:[K;4],beta:K,finals:&[K;4],
    workspace:&mut[K],kernel:&r17_weighted_groups::Kernel,coins:&[K])->K {
    assert!(workspace.len()>=531 && coins.len()>=271);
    if let Some(result)=r106_try_terminal(audit,abc,alpha,beta,finals,kernel,coins) {return result;}
    // Raw/noncanonical caller behavior remains at the retained boundary.
    let ordinary=terminal_scalar(audit,abc,alpha,beta,finals,workspace,kernel);
    let sparse=r81_sparse_scalar_after_ordinary(coins,workspace,kernel);
    ordinary.add(sparse.mul(beta.mul(audit[10])))
}
#[cfg(not(target_os="solana"))]
pub(super) fn r106_controls() {
    use corelib::field::{CM31,P};
    let mut rng=0x106ae3721098c47u64;
    fn sample(r:&mut u64)->K {
        let mut m=||{*r^=*r<<13;*r^=*r>>7;*r^=*r<<17;M31((*r%u64::from(corelib::field::P))as u32)};
        K{c0:CM31::new(m(),m()),c1:CM31::new(m(),m())}
    }
    let mut geometry=0;let mut inactive=0;
    for case in 0..512 {
        let mut next=||match case {0=>K::ZERO,1=>K::ONE,2=>K{c0:CM31::new(M31(P-1),M31(P-1)),c1:CM31::new(M31(P-1),M31(P-1))},_=>sample(&mut rng)};
        let high=core::array::from_fn(|_|next());let finals=core::array::from_fn(|_|next());
        let mut hb=vec![CQ::ZERO;128];r106_geometry(&r85_convert(high).unwrap(),&r85_convert(finals).unwrap(),&mut hb);
        let mut old=vec![K::ZERO;128];scalar_geometry(&high,&finals,&mut old);
        assert_eq!(hb.iter().copied().map(r85_out).collect::<Vec<_>>(),old);geometry+=128;
        let q=r106_inactive(&hb);let mut expected=[K::ZERO;19];r24_inactive_values(&old,&mut expected);
        assert_eq!(q.map(r85_out),expected);inactive+=19;
        let audit=core::array::from_fn(|_|next());let abc=core::array::from_fn(|_|next());
        let alpha=core::array::from_fn(|_|next());let beta=if case%3==0{K::ZERO}else if case%3==1{K::ONE}else{next()};
        let coins:Vec<_>=(0..271).map(|_|next()).collect();let kernel=r17_weighted_groups::Kernel::new(abc,alpha);
        let mut workspace=vec![K::ZERO;531];
        let ordinary=terminal_scalar(&audit,abc,alpha,beta,&finals,&mut workspace,&kernel);
        let sparse=r81_sparse_scalar_after_ordinary(&coins,&workspace,&kernel);
        let expected=ordinary.add(sparse.mul(beta.mul(audit[10])));
        assert_eq!(r106_try_terminal(&audit,abc,alpha,beta,&finals,&kernel,&coins),Some(expected));
        assert_eq!(r106_terminal(&audit,abc,alpha,beta,&finals,&mut workspace,&kernel,&coins),expected);
    }
    // All 128 basis directions bind the generated integer adder schedule.
    for row in 0..128 {
        let mut hb=vec![CQ::ZERO;128];hb[row]=CQ::ONE;
        let raw:Vec<_>=hb.iter().copied().map(r85_out).collect();
        let mut expected=[K::ZERO;19];r24_inactive_values(&raw,&mut expected);
        assert_eq!(r106_inactive(&hb).map(r85_out),expected);inactive+=19;
    }
    let kernel=r17_weighted_groups::Kernel::new([K::ONE;3],[K::ONE;4]);let mut malformed=0;
    for row in 0..271 {for limb in 0..4 {for bad in [P,P+1,u32::MAX] {
        let mut coins=vec![K::ONE;271];let mut raw=[M31::ZERO;4];raw[limb]=M31(bad);
        coins[row]=K{c0:CM31::new(raw[0],raw[1]),c1:CM31::new(raw[2],raw[3])};
        // beta zero is deliberately not allowed to bypass validation.
        assert_eq!(r106_try_terminal(&[K::ONE;11],[K::ONE;3],[K::ONE;4],K::ZERO,&[K::ONE;4],&kernel,&coins),None);malformed+=1;
    }}}
    println!("R106_TERMINAL profiles=512 geometry_coordinates={geometry} inactive_coordinates={inactive} malformed={malformed} exact_adder_coefficients=true beta_zero_one=true");
}
