fn XRi_shipped_prepared_claim<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            let mut dot=crate::fast_pairing::EbyKDot::new();
            for l in 0..29 {
                let scalar=match point {0..=2=>sem.claims[point][l],3=>sem.extra[l],4=>sem.before_z1[l],_=>field(y1,l).c0()};
                dot.push(g[l],scalar).map_err(|_|Error::Parse)?;
            }
            parts[point+1]=dot.finish();
        }
        let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        Ok(claim)
}

fn XRi_shipped_echeck(b:&[u8],k:bool)->Result<(),Error> {
    for c in b.chunks_exact(32) {let x=E::from_le_bytes(c).ok_or(Error::Parse)?;if k&&x.c1()!=K::ZERO {return Err(Error::Parse);}}
    Ok(())
}

fn XRi_shipped_put(out:&mut Vec<u8>,x:E) {out.extend_from_slice(&x.to_le_bytes());}

fn XRi_shipped_put_k(out:&mut Vec<u8>,x:K) {let mut b=[0;16];x.write_le_bytes(&mut b);out.extend_from_slice(&b);}

fn XRi_shipped_wide_view<'a>(proof: &'a [u8], semantic: &'a [u8], y1: &'a [u8]) -> Result<View<'a>, Error> {
    Ok(View {
        variant: Variant::S2,
        semantic,
        y1,
        inactive: E::from_le_bytes(&proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]).ok_or(Error::Parse)?,
        round0: &proof[compact::OFF_ROUND0..compact::OFF_FOLDED_ROOT],
        folded_root: Some(proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap()),
        round1: &proof[compact::OFF_ROUND1..compact::OFF_FINAL],
        final_message: &proof[compact::OFF_FINAL..compact::OFF_OPENINGS],
        query_bytes: &[],
    })
}
