// Owned safe references. These definitions carry no equivalence claim by themselves.
fn XRf_reference_prepared_claim<H:Digest32>(sem:&r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
    let k=powers::<7>(kappa);
    let mut parts=[E::ZERO;7];
    parts[0]=inactive;
    let mut point=0;
    while point<6 {
        let mut dot=fast_pairing::EbyKDot::new();
        let mut l=0;
        while l<29 {
            let scalar=if point<3 {sem.claims[point][l]} else if point==3 {sem.extra[l]} else if point==4 {sem.before_z1[l]} else {field(y1,l).c0()};
            if dot.push(g[l],scalar).is_err() {return Err(Error::Parse)}
            l+=1;
        }
        parts[point+1]=dot.finish();
        point+=1;
    }
    let mut claim=E::ZERO;
    let mut i=0;
    while i<7 {
        trace::value(14,i,parts[i]);
        claim=claim.add(k[i].mul(parts[i]));
        i+=1;
    }
    trace::value(14,7,claim);
    Ok(claim)
}
fn XRf_reference_check_values(bytes:&[u8])->Result<(),compact::CodecError> {
    let mut at=0;
    while at+16<=bytes.len() {
        for j in 0..4 {
            let mut raw=[0;4];raw.copy_from_slice(&bytes[at+4*j..at+4*j+4]);
            if u32::from_le_bytes(raw)>=0x7fff_ffff {return Err(compact::CodecError::NonCanonical)}
        }
        at+=16;
    }
    Ok(())
}
fn XRf_reference_expand_values(bytes:&[u8],out:&mut[u8])->Result<(),compact::CodecError> {
    if bytes.len()%16!=0 || out.len()!=2*bytes.len() {return Err(compact::CodecError::Length)}
    let mut i=0;
    while i<bytes.len()/16 {
        let mut j=0;
        while j<32 {out[32*i+j]=if j<16 {bytes[16*i+j]} else {0};j+=1;}
        i+=1;
    }
    Ok(())
}
fn XRf_reference_echeck(bytes:&[u8],k:bool)->Result<(),Error> {
    let mut at=0;
    while at+32<=bytes.len() {
        for j in 0..8 {
            let mut raw=[0;4];raw.copy_from_slice(&bytes[at+4*j..at+4*j+4]);
            let x=u32::from_le_bytes(raw);
            if x>=0x7fff_ffff || (k&&j>=4&&x!=0) {return Err(Error::Parse)}
        }
        at+=32;
    }
    Ok(())
}
fn XRf_reference_wide_view<'a>(proof:&'a[u8],semantic:&'a[u8],y1:&'a[u8])->Result<View<'a>,Error> {
    let inactive=E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?;
    let root:&[u8;32]=proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();
    Ok(View {variant:Variant::S2,semantic,y1,inactive,
      round0:&proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],folded_root:Some(root),
      round1:&proof[compact::OFF_ROUND1..compact::OFF_FINAL],final_message:&proof[compact::OFF_FINAL..compact::OFF_OPENINGS],query_bytes:&[]})
}
fn XRf_reference_put(out:&mut Vec<u8>,x:E) {for b in x.to_le_bytes() {out.push(b)}}
fn XRf_reference_put_k(out:&mut Vec<u8>,x:K) {
    for limb in [x.c0.a.0,x.c0.b.0,x.c1.a.0,x.c1.b.0] {for b in limb.to_le_bytes() {out.push(b)}}
}
fn XRf_reference_checkpoint<H:Digest32>(p:&Prepared,a:&Accumulator,proof:&[u8],public:&[u8],hash:H)->Vec<u8> {
    let mut out=Vec::with_capacity(checkpoint_size(p.variant));
    for b in b"R1P2CKP2" {out.push(*b)}
    for b in [p.variant.tag(),a.next as u8,1,0,0,0,0,0] {out.push(b)}
    for b in hash.digest(&[proof]) {out.push(b)}
    for b in hash.digest(&[public]) {out.push(b)}
    for b in p.state {out.push(b)}
    for root in p.roots {for b in root {out.push(b)}}
    for x in [p.gamma,p.kappa,p.alpha[0],p.alpha[1]] {XRf_reference_put(&mut out,x)}
    XRf_reference_put_k(&mut out,p.rho);
    for q in p.queries {for b in q.to_le_bytes() {out.push(b)}}
    for x in p.semantic_alpha {XRf_reference_put_k(&mut out,x)}
    for z in p.z {for x in [z.x,z.y] {XRf_reference_put_k(&mut out,x)}}
    for x in [p.claim,a.rhs] {XRf_reference_put(&mut out,x)}
    XRf_reference_put_k(&mut out,a.power);
    for x in &a.weights {XRf_reference_put_k(&mut out,*x)}
    for b in hash.digest(&[b"UNPROVED:R1:checkpoint",&out]) {out.push(b)}
    assert_eq!(out.len(),checkpoint_size(p.variant));out
}
