#[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,0));for s in 0..4 {crate::trace::value(9,4*i+s,dots[s]);}
    let inverse=geometry.for_query(i);
    let mut folded=circle_fold_with_inverses(p.alpha[0],dots,inverse);crate::trace::value(10,2*i,folded);#[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,1));
    if p.variant.folds()==2 {
        let values=core::array::from_fn(|s|field(&q[INITIAL_QUERY_BYTES..],s));
        if folded!=values[u%4] {return Err(Error::Query);}
        folded=line_fold_with_inverses(p.alpha[1],values,inverse);crate::trace::value(10,2*i+1,folded);
    }
    #[cfg(feature="detail-phases")]mark(obs,Phase::QueryPart(i,2));
