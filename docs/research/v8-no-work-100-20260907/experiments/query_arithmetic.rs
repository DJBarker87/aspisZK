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
#[inline(never)]
pub(super) fn gamma(c1:&[u8],c2:&[u8],powers:&StateOnlySpendQueryPowers)->Result<[K;4],Error>{
    let c1=decode::<104>(c1)?;let c2=decode::<48>(c2)?;
    let mut out=[K::ZERO;4];
    for slot in 0..4{
        #[cfg(v8_gamma_fixed)]
        let fields={
            let values:&[u32;26]=c1[26*slot..26*(slot+1)].try_into().unwrap();
            let p=&powers.base.c1_limbs;
            [fixed_dot::<0>(values,p),fixed_dot::<1>(values,p),
             fixed_dot::<2>(values,p),fixed_dot::<3>(values,p)]
        };
        #[cfg(not(v8_gamma_fixed))]
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
