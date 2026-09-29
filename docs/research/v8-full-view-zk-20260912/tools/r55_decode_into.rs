// Caller-owned decoded storage: no Result<[u32;N],Error> payload copies.
// The bytes, unpacking order, length check and canonicality remain identical.
#[inline(never)]
fn r55_decode_into<const N:usize>(bytes:&[u8],out:&mut[u32;N])->Result<(),Error>{
    if N==0 || N%8!=0 || bytes.len()!=N/8*31{return Err(Error::Length);}
    let mut invalid=0u32;
    for (block,b) in bytes.chunks_exact(31).enumerate(){
        let load=|j|u64::from_le_bytes(b[j..j+8].try_into().unwrap());
        let (w0,w1,w2,w3)=(load(0),load(8),load(16),load(23)>>8);
        let v=[w0,w0>>31,(w0>>62)|(w1<<2),w1>>29,(w1>>60)|(w2<<4),w2>>27,(w2>>58)|(w3<<6),w3>>25];
        for j in 0..8{
            let value=(v[j]&u64::from(corelib::field::P))as u32;
            out[8*block+j]=value;
            invalid|=u32::from(value==corelib::field::P);
        }
    }
    if invalid!=0{Err(Error::Canonical)}else{Ok(())}
}
