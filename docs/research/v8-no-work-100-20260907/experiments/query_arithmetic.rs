//! Research-only gamma recombination, same canonical packed records.
//! Four-word unpacking and explicit four-term u64 dots. Every dot starts at
//! zero. Canonical factors satisfy 4*(p-1)^2 < 2^64; wrapping_add is therefore
//! exact integer addition, NOT field arithmetic modulo 2^64.
use super::*;
#[inline(always)]
fn reduce_chunk(raw:u64)->u64{
    #[cfg(v8_gamma_partial)]
    { (raw & u64::from(corelib::field::P)).wrapping_add(raw>>31) }
    #[cfg(not(v8_gamma_partial))]
    { u64::from(M31::reduce_u64(raw).0) }
}
fn decode<const N:usize>(bytes:&[u8])->Result<[u32;N],Error>{
    if N==0 || N%8!=0 || bytes.len()!=N/8*31{return Err(Error::Length);}
    let mut out=[0u32;N];let mut invalid=0u32;
    for (block,b) in bytes.chunks_exact(31).enumerate(){
        let load=|j|u64::from_le_bytes(b[j..j+8].try_into().unwrap());
        let (w0,w1,w2,w3)=(load(0),load(8),load(16),load(23)>>8);
        let v=[w0,w0>>31,(w0>>62)|(w1<<2),w1>>29,(w1>>60)|(w2<<4),w2>>27,(w2>>58)|(w3<<6),w3>>25];
        for j in 0..8{let value=(v[j]&u64::from(corelib::field::P)) as u32;
            out[8*block+j]=value;invalid|=u32::from(value==corelib::field::P);
        }
    }
    if invalid!=0{Err(Error::Canonical)}else{Ok(out)}
}
#[cfg(v8_decode_blocks)]
fn decode_blocks<const B:usize>(bytes:&[u8])->Result<[[u32;8];B],Error>{
    if B==0 || bytes.len()!=B*31{return Err(Error::Length);}
    let mut invalid=0u32;
    let out=core::array::from_fn(|block|{
        let b=&bytes[31*block..31*(block+1)];
        let load=|j|u64::from_le_bytes(b[j..j+8].try_into().unwrap());
        let (w0,w1,w2,w3)=(load(0),load(8),load(16),load(23)>>8);
        let values=[w0,w0>>31,(w0>>62)|(w1<<2),w1>>29,(w1>>60)|(w2<<4),w2>>27,(w2>>58)|(w3<<6),w3>>25]
            .map(|x|(x&u64::from(corelib::field::P)) as u32);
        for &v in &values{invalid|=u32::from(v==corelib::field::P);}
        values
    });
    if invalid!=0{Err(Error::Canonical)}else{Ok(out)}
}
#[inline(never)]
pub(super) fn gamma(c1:&[u8],c2:&[u8],powers:&StateOnlySpendQueryPowers)->Result<[K;4],Error>{
    #[cfg(v8_decode_profile)] query_checkpoint("v8:gamma-enter");
    #[cfg(not(v8_decode_blocks))]
    let c1=decode::<104>(c1)?;
    #[cfg(v8_decode_blocks)]
    let c1_blocks=decode_blocks::<13>(c1)?;
    #[cfg(v8_decode_blocks)]
    let c1=c1_blocks.as_flattened();
    #[cfg(v8_decode_profile)] query_checkpoint("v8:decode-c1");
    #[cfg(not(v8_decode_blocks))]
    let c2=decode::<48>(c2)?;
    #[cfg(v8_decode_blocks)]
    let c2_blocks=decode_blocks::<6>(c2)?;
    #[cfg(v8_decode_blocks)]
    let c2=c2_blocks.as_flattened();
    #[cfg(v8_decode_profile)] query_checkpoint("v8:decode-c2");
    let mut out=[K::ZERO;4];
    for slot in 0..4{
        #[cfg(v8_gamma_fused)]
        let fields=fused_dot(c1[26*slot..26*(slot+1)].try_into().unwrap(),&powers.base.c1_limbs);
        #[cfg(all(v8_gamma_fixed,not(v8_gamma_fused)))]
        let fields={
            let values:&[u32;26]=c1[26*slot..26*(slot+1)].try_into().unwrap();
            let p=&powers.base.c1_limbs;
            [fixed_dot::<0>(values,p),fixed_dot::<1>(values,p),
             fixed_dot::<2>(values,p),fixed_dot::<3>(values,p)]
        };
        #[cfg(not(any(v8_gamma_fixed,v8_gamma_fused)))]
        let fields={
        let mut sum=[0u64;4];
        for start in (0..24).step_by(4){
            let v=core::array::from_fn::<_,4,_>(|i|u64::from(c1[26*slot+start+i]));
            let p=&powers.base.c1_limbs;
            for limb in 0..4{
                let raw=(u64::from(p[start][limb])*v[0])
                    .wrapping_add(u64::from(p[start+1][limb])*v[1])
                    .wrapping_add(u64::from(p[start+2][limb])*v[2])
                    .wrapping_add(u64::from(p[start+3][limb])*v[3]);
                // Seven chunks, each partial reduction <5p. Every prefix
                // is <35p<2^37, including maximal canonical inputs.
                sum[limb]=sum[limb].wrapping_add(reduce_chunk(raw));
            }
        }
        for limb in 0..4{
            let raw=u64::from(powers.base.c1_limbs[24][limb])*u64::from(c1[26*slot+24])
                +u64::from(powers.base.c1_limbs[25][limb])*u64::from(c1[26*slot+25]);
            sum[limb]=sum[limb].wrapping_add(reduce_chunk(raw));
        }
        sum.map(M31::reduce_u64)
        };
        let value=K{c0:CM31::new(fields[0],fields[1]),c1:CM31::new(fields[2],fields[3])};
        let helpers=core::array::from_fn(|h|{let offset=4*(4*h+slot);K{c0:CM31::new(M31(c2[offset]),M31(c2[offset+1])),c1:CM31::new(M31(c2[offset+2]),M31(c2[offset+3]))}});
        out[slot]=value.add(corelib::field::qm31_sum_products3_prepared(&[powers.base.helpers[0],powers.base.helpers[1],powers.d],&helpers));
    }
    #[cfg(v8_decode_profile)] query_checkpoint("v8:gamma-dots");
    Ok(out)
}

// Same six four-product chunks and final pair; only indices and limb choice
// become constants. No assumption about gamma^0, helper values or honest zeros.
#[cfg(v8_gamma_fixed)]
#[inline(always)]
fn fixed_dot<const L:usize>(v:&[u32;26],p:&[[u32;4];26])->M31{
    macro_rules! chunk {($i:expr)=>{reduce_chunk(
        (u64::from(p[$i][L])*u64::from(v[$i]))
        .wrapping_add(u64::from(p[$i+1][L])*u64::from(v[$i+1]))
        .wrapping_add(u64::from(p[$i+2][L])*u64::from(v[$i+2]))
        .wrapping_add(u64::from(p[$i+3][L])*u64::from(v[$i+3])))}}
    let tail=reduce_chunk(u64::from(p[24][L])*u64::from(v[24])
        +u64::from(p[25][L])*u64::from(v[25]));
    let a=chunk!(0).wrapping_add(chunk!(4));
    let b=chunk!(8).wrapping_add(chunk!(12));
    let c=chunk!(16).wrapping_add(chunk!(20));
    M31::reduce_u64(a.wrapping_add(b).wrapping_add(c.wrapping_add(tail)))
}

// Control: one loaded four-value block feeds all four channels. Same seven
// reductions and balanced final additions as fixed_dot; no special power or
// honest-input assumption. A larger live working set may regress SBF.
#[cfg(v8_gamma_fused)]
#[inline(always)]
fn fused_chunk<const S:usize>(v:&[u32;26],p:&[[u32;4];26])->[u64;4]{
    let [a,b,c,d]=[v[S],v[S+1],v[S+2],v[S+3]].map(u64::from);
    core::array::from_fn(|l|reduce_chunk((u64::from(p[S][l])*a)
        .wrapping_add(u64::from(p[S+1][l])*b)
        .wrapping_add(u64::from(p[S+2][l])*c)
        .wrapping_add(u64::from(p[S+3][l])*d)))
}
#[cfg(v8_gamma_fused)]
#[inline(always)]
fn fused_dot(v:&[u32;26],p:&[[u32;4];26])->[M31;4]{
    let a=fused_chunk::<0>(v,p);let b=fused_chunk::<4>(v,p);
    let c=fused_chunk::<8>(v,p);let d=fused_chunk::<12>(v,p);
    let e=fused_chunk::<16>(v,p);let f=fused_chunk::<20>(v,p);
    let tail:[u64;4]=core::array::from_fn(|l|reduce_chunk(
        u64::from(p[24][l])*u64::from(v[24])+u64::from(p[25][l])*u64::from(v[25])));
    core::array::from_fn(|l|M31::reduce_u64(a[l].wrapping_add(b[l])
        .wrapping_add(c[l].wrapping_add(d[l]))
        .wrapping_add(e[l].wrapping_add(f[l]).wrapping_add(tail[l]))))
}

#[cfg(all(test,v8_gamma_fused))]
mod fused_tests {
    use super::*;
    #[test]
    fn arbitrary_channels_match_wide_reference(){
        let mut rng=0x6675_7365_6420_7638u64;
        let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(corelib::field::P)) as u32};
        for case in 0..2048{
            let mut v=core::array::from_fn(|_|next());
            let mut p=core::array::from_fn(|_|core::array::from_fn(|_|next()));
            if case==0{v=[0;26];p=[[0;4];26];}
            if case==1{v=[corelib::field::P-1;26];p=[[corelib::field::P-1;4];26];}
            if (2..28).contains(&case){v=[0;26];v[case-2]=corelib::field::P-1;}
            let expected=core::array::from_fn(|l|M31(((0..26).map(|i|u128::from(v[i])*u128::from(p[i][l])).sum::<u128>()%u128::from(corelib::field::P)) as u32));
            let fixed=[fixed_dot::<0>(&v,&p),fixed_dot::<1>(&v,&p),fixed_dot::<2>(&v,&p),fixed_dot::<3>(&v,&p)];
            assert_eq!(fused_dot(&v,&p),expected);assert_eq!(fixed,expected);
        }
        controls(); // actual packed gamma, all 152 invalid positions and short inputs
    }
}

#[cfg(all(test,v8_decode_blocks))]
mod decode_tests {
    use super::*;
    #[test]
    fn direct_blocks_match_flat_decoder_and_rejections(){
        let mut rng=0x6465_636f_6465_7638u64;
        let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;rng as u8};
        for case in 0..2048{
            let mut a:[u8;403]=core::array::from_fn(|_|next());
            let mut b:[u8;186]=core::array::from_fn(|_|next());
            if case==0{a.fill(0);b.fill(0);}
            if case==1{a.fill(255);b.fill(255);}
            assert_eq!(decode_blocks::<13>(&a).map(|v|v.as_flattened().to_vec()),decode::<104>(&a).map(|v|v.to_vec()));
            assert_eq!(decode_blocks::<6>(&b).map(|v|v.as_flattened().to_vec()),decode::<48>(&b).map(|v|v.to_vec()));
        }
        for n in 0..=404{if n!=403{assert_eq!(decode_blocks::<13>(&vec![0;n]),Err(Error::Length));}}
        for n in 0..=187{if n!=186{assert_eq!(decode_blocks::<6>(&vec![0;n]),Err(Error::Length));}}
        assert_eq!(decode_blocks::<0>(&[]),Err(Error::Length));
        controls();
    }
}
#[cfg(not(v8_performance_sbf))]
pub(super) fn controls(){
    fn pack(values:&[u32])->Vec<u8>{
        let mut out=vec![0;values.len()*31/8];
        for(i,x)in values.iter().enumerate(){for bit in 0..31{if x&(1<<bit)!=0{let at=i*31+bit;out[at/8]|=1<<(at%8);}}}out
    }
    let p=corelib::field::P;
    for seed in 0..512u32{
        let values:Vec<u32>=(0..152).map(|j|if seed==0{0}else if seed==1{p-1}
            else if seed<154{if j==seed-2{p-1}else{0}}
            else{(j*1_000_003+seed*19)%p}).collect();
        let a=pack(&values[..104]);let b=pack(&values[104..]);
        let gamma=K{c0:CM31::new(M31(seed),M31(p-1-seed)),c1:CM31::new(M31(seed+2),M31(seed+3))};
        let powers=StateOnlySpendQueryPowers::new(gamma);
        assert_eq!(decode::<104>(&a).unwrap().as_slice(),&values[..104]);
        assert_eq!(decode::<48>(&b).unwrap().as_slice(),&values[104..]);
        assert_eq!(self::gamma(&a,&b,&powers).unwrap(),gamma_combine_v6_packed_layer0(&a,&b,&powers).unwrap());
    }
    let powers=StateOnlySpendQueryPowers::new(K::ONE);
    // Maximal canonical limbs, independently of whether they form a power
    // sequence: this exercises the actual four-product integer bound.
    let mut max_powers=powers;
    max_powers.base.c1_limbs=[[p-1;4];26];
    let a=pack(&vec![p-1;104]);let b=pack(&vec![p-1;48]);
    assert_eq!(gamma(&a,&b,&max_powers).unwrap(),
        gamma_combine_v6_packed_layer0(&a,&b,&max_powers).unwrap());
    for bad in 0..152{
        let mut values=vec![0;152];values[bad]=p;
        let a=pack(&values[..104]);let b=pack(&values[104..]);
        assert_eq!(gamma(&a,&b,&powers),Err(Error::Canonical));
        assert!(gamma_combine_v6_packed_layer0(&a,&b,&powers).is_err());
    }
    assert!(gamma(&[0;402],&[0;186],&powers).is_err());
    assert!(gamma(&[0;403],&[0;185],&powers).is_err());
    println!("GAMMA_CONTROLS canonical_profiles=512 maximal_limb_dot=true noncanonical_positions=152 short_inputs=2");
}
