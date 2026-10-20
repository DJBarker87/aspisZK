fn finish_relation(v:&View<'_>,p:&Prepared,a:&Accumulator,obs:Observer)->Result<(),Error> {
    let mut claim=p.claim;
    for round in 0..p.variant.folds() {
        let poly=if round==0 {v.round0}else{v.round1};
        let lhs=field(poly,0).add(field(poly,4));let rhs=claim.mul_m31(QUARTER);
        crate::trace::value(15,3*round,lhs);crate::trace::value(15,3*round+1,rhs);
        if lhs!=rhs {return Err(Error::Relation);}
        claim=polynomial(poly,p.alpha[round]);crate::trace::value(15,3*round+2,claim);
    }
    let weights=Weights::new(p.variant,&p.semantic_alpha,&p.z)?;
    let pair=weights.pair(&p.alpha[..p.variant.folds()],v.final_message,p.kappa)?;
    crate::trace::value(16,0,pair);crate::trace::value(16,1,claim);
    if pair!=claim {return Err(Error::Relation);}
    mark(obs,Phase::Relation);
    let mut dot=crate::fast_pairing::EbyKDot::new();
    for (j,w) in a.weights.iter().enumerate() {dot.push(field(v.final_message,j),*w).map_err(|_|Error::Parse)?;}
    let actual=dot.finish();
    crate::trace::value(17,0,actual);crate::trace::value(17,1,a.rhs);
    if a.next!=22||actual!=a.rhs {return Err(Error::Query);}
    mark(obs,Phase::Final);Ok(())
}