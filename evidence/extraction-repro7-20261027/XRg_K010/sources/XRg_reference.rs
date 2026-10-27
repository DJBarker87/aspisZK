// Owned safe reference for predecoded claims storage only; Prefix/allocator association OPEN.
fn XRg_claims_reference(rows: [Result<[K;29],Error>;3]) -> Result<Box<[[K;29];3]>,Error> {
    let a=rows[0]?; let b=rows[1]?; let c=rows[2]?;
    Ok(Box::new([a,b,c]))
}
// Owned byte reference for ValidatedRecord::decode_k, including checked range errors.
fn XRg_decode_reference<const N:usize>(row:u8,framed:&[u8],offset:usize)->Result<[K;N],Error> {
    if row<14 {return Err(Error::InvalidRow)}
    let start=offset.checked_mul(32).ok_or(Error::Length{row})?;
    let size=N.checked_mul(32).ok_or(Error::Length{row})?;
    let end=start.checked_add(size).ok_or(Error::Length{row})?;
    let payload=&framed[5..];
    if end>payload.len() {return Err(Error::Length{row})}
    let mut out=[K::ZERO;N];
    let mut i=0;
    while i<N {
        let mut limbs=[0u32;4];
        for j in 0..4 {let at=start+32*i+4*j; limbs[j]=u32::from_le_bytes(payload[at..at+4].try_into().unwrap());}
        if limbs.iter().any(|x| *x>=2147483647) {return Err(Error::NonCanonical{row,value:offset+i})}
        out[i]=K::from_le_bytes(&payload[start+32*i..start+32*i+16]).unwrap();
        i+=1;
    }
    Ok(out)
}

fn XRg_validate_reference(row:u8,bytes:&[u8])->Result<(),Error>{
    let mut i=0;
    while i<bytes.len()/32 {
        for j in 0..8 {let at=32*i+4*j; let x=u32::from_le_bytes(bytes[at..at+4].try_into().unwrap());
            if x>=2147483647 || (j>=4 && x!=0) {return Err(Error::NonCanonical{row,value:i})}
        }
        i+=1;
    }
    Ok(())
}

// Source starts the fold at polynomial[0] then visits all 28 entries (first twice).
fn XRg_boundary_reference(polynomial:&[K;28])->K{
    let mut out=polynomial[0].add(polynomial[0]);
    for i in 1..28 {out=out.add(polynomial[i]);}
    out
}

fn XRg_dot_reference(sums:[u64;4],raw:[u64;4],i:usize)->u64{
    sums[i].wrapping_add((raw[i] % (1u64<<31)).wrapping_add(raw[i]/(1u64<<31)))
}

fn XRg_fallback_reference(second:bool)->aspis_core::circle::SecureCirclePoint {
    aspis_core::transcript::circle_fallback_point(usize::from(second))
}
