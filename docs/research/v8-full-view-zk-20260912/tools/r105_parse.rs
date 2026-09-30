//! Same fixed canonical field bytes, with an alignment-checked read boundary.
use super::*;
#[inline(never)]
pub(super) fn fields(bytes:&[u8])->Result<Vec<K>,Error>{
    if bytes.len()%16!=0{return Err(Error::Length);}
    #[cfg(target_endian="little")]
    {
        // u32 admits every bit pattern; align_to establishes proper alignment.
        let (prefix,words,suffix)=unsafe {bytes.align_to::<u32>()};
        if prefix.is_empty() && suffix.is_empty(){
            let mut out=Vec::with_capacity(bytes.len()/16);let mut invalid=0u32;
            for v in words.chunks_exact(4){
                for &x in v{invalid|=x|x.wrapping_add(1);}
                out.push(K{c0:CM31::new(M31(v[0]),M31(v[1])),c1:CM31::new(M31(v[2]),M31(v[3]))});
            }
            return if invalid>>31!=0{Err(Error::Canonical)}else{Ok(out)};
        }
    }
    bytes.chunks_exact(16).map(|x|K::from_le_bytes(x).ok_or(Error::Canonical)).collect()
}
#[cfg(not(target_os="solana"))]
pub(super) fn controls(){
    let mut seed=0x105e_401a_7721_1893u64;
    let mut next=||{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;(seed%u64::from(corelib::field::P))as u32};
    let mut good=0;let mut bad=0;
    for n in [0,1,4,27,29,256,699]{for case in 0..32{for offset in 0..4{
        let mut b=vec![0;offset];
        for _ in 0..4*n{let x=if case==0{0}else if case==1{corelib::field::P-1}else{next()};b.extend(x.to_le_bytes());}
        let input=&b[offset..];let expected=input.chunks_exact(16).map(|x|K::from_le_bytes(x).ok_or(Error::Canonical)).collect();
        assert_eq!(fields(input),expected);good+=1;
    }}}
    for offset in 0..4{for word in 0..4*699{for x in [corelib::field::P,1<<31,u32::MAX]{
        let mut b=vec![0;offset+16*699];let at=offset+4*word;b[at..at+4].copy_from_slice(&x.to_le_bytes());
        assert_eq!(fields(&b[offset..]),Err(Error::Canonical));bad+=1;
    }}}
    for n in 0..100{if n%16!=0{assert_eq!(fields(&vec![0;n]),Err(Error::Length));bad+=1;}}
    println!("R105_PARSE accepted_comparisons={good} malformed={bad} offsets=4 fields=699 original_bytes=true all_fields_validated=true");
}
