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