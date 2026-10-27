fn owned_scalar(claims:&[[K;29];3],extra:&[K;29],before_z1:&[K;29],y1:&[u8],point:usize,l:usize)->K { match point {0..=2=>claims[point][l],3=>extra[l],4=>before_z1[l],_=>field(y1,l).c0()} }
fn owned_push(mut dot:crate::fast_pairing::EbyKDot,g:&[E;29],l:usize,scalar:K)->(Result<(),()>,crate::fast_pairing::EbyKDot) { let r=dot.push(g[l],scalar); (r,dot) }
fn owned_sum(k:&[E;7],parts:&[E;7])->E {         let mut claim=E::ZERO;
        for i in 0..7 {crate::trace::value(14,i,parts[i]);claim=claim.add(k[i].mul(parts[i]));}
        crate::trace::value(14,7,claim);
        claim }
fn owned_claim_loops(claims:&[[K;29];3],extra:&[K;29],before_z1:&[K;29],y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> {
        let k=powers::<7>(kappa);
        let mut parts=[E::ZERO;7];parts[0]=inactive;
        for point in 0..6 {
            let mut dot=crate::fast_pairing::EbyKDot::new();
            for l in 0..29 {
                let scalar=owned_scalar(claims,extra,before_z1,y1,point,l);
                let (r,next)=owned_push(dot,g,l,scalar);dot=next;if r.is_err() { return Err(Error::Parse); }
            }
            parts[point+1]=dot.finish();
        }
        Ok(owned_sum(&k,&parts))
}
pub fn prepared_claim_owned<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error> { owned_claim_loops(&*sem.claims,&sem.extra,&sem.before_z1,y1,inactive,g,kappa) }
