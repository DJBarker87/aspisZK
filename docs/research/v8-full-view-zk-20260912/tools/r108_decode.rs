// Same 31-bit packed encoding. Only the interior aligned u64 words are
// borrowed; edge limbs use bounded byte reads. No reads outside `bytes`.
#[inline(never)]
fn r55_decode_into<const N:usize>(bytes:&[u8],out:&mut[u32;N])->Result<(),Error> {
    if N==0 || N%8!=0 || bytes.len()!=N/8*31 {return Err(Error::Length);}
    #[cfg(target_endian="little")]
    {
        // All bit patterns are valid u64 values. align_to supplies aligned
        // interior words; field canonicality is checked independently below.
        let (prefix,words,_suffix)=unsafe{bytes.align_to::<u64>()};
        let first=8*prefix.len();let end=first+64*words.len();let mut invalid=0u32;
        for i in 0..N {
            let bit=31*i;
            let value=if bit>=first && bit+31<=end {
                let at=bit-first;let shift=at&63;let word=at>>6;
                let mut raw=words[word]>>shift;
                if shift>33 {raw|=words[word+1]<<(64-shift);}
                (raw&u64::from(corelib::field::P))as u32
            } else {
                let start=bit>>3;let shift=bit&7;let count=(shift+31+7)>>3;
                let mut raw=0u64;
                for j in 0..count {raw|=u64::from(bytes[start+j])<<(8*j);}
                ((raw>>shift)&u64::from(corelib::field::P))as u32
            };
            out[i]=value;invalid|=value+1;
        }
        return if invalid>>31==0 {Ok(())}else{Err(Error::Canonical)};
    }
    #[cfg(not(target_endian="little"))]
    r108_retained_decode(bytes,out)
}
#[cfg(not(v8_performance_sbf))]
pub(super) fn r108_controls() {
    fn pack(values:&[u32])->Vec<u8> {
        let mut b=vec![0;values.len()*31/8];
        for(i,x)in values.iter().enumerate(){for bit in 0..31{if x&(1<<bit)!=0{let at=31*i+bit;b[at/8]|=1<<(at%8);}}}b
    }
    fn check<const N:usize>(values:&[u32;N],offset:usize)->bool {
        let packed=pack(values);let mut b=vec![37;offset];b.extend_from_slice(&packed);b.extend_from_slice(&[53;8]);
        let bytes=&b[offset..offset+packed.len()];let mut old=[0;N];let mut new=[u32::MAX;N];
        let a=r108_retained_decode(bytes,&mut old);let c=r55_decode_into(bytes,&mut new);assert_eq!(a,c);
        if a.is_ok(){assert_eq!(old,new);assert_eq!(&new,values);true}else{false}
    }
    let mut rng=0x108de_82749e82au64;
    let mut next=||{rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;(rng%u64::from(corelib::field::P))as u32};
    let mut accepted=0;let mut malformed=0;
    for case in 0..2048 {
        let all:[u32;152]=core::array::from_fn(|i|if case==0{0}else if case==1{corelib::field::P-1}
            else if case<154{if i==case-2{corelib::field::P-1}else{0}}else{next()});
        for offset in 0..8 {
            assert!(check::<104>(all[..104].try_into().unwrap(),offset));
            assert!(check::<48>(all[104..].try_into().unwrap(),offset));accepted+=2;
        }
    }
    for bad in 0..152 {for offset in 0..8 {
        let mut all=[0;152];all[bad]=corelib::field::P;
        if bad<104{assert!(!check::<104>(all[..104].try_into().unwrap(),offset));}
        else{assert!(!check::<48>(all[104..].try_into().unwrap(),offset));}malformed+=1;
    }}
    for n in 0..=404 {if n!=403 {assert_eq!(r55_decode_into(&vec![0;n],&mut[0;104]),Err(Error::Length));malformed+=1;}}
    for n in 0..=187 {if n!=186 {assert_eq!(r55_decode_into(&vec![0;n],&mut[0;48]),Err(Error::Length));malformed+=1;}}
    assert_eq!(r55_decode_into::<0>(&[],&mut[]),Err(Error::Length));
    println!("R108_DECODE accepted_comparisons={accepted} malformed={malformed} offsets=8 exact_bytes=true all_152_canonicality_positions=true");
}
