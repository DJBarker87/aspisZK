fn mark(obs: crate::verifier::Observer, i: u8) {
    #[cfg(feature="detail-phases")]
    if let Some(f)=obs {f(crate::verifier::Phase::SemanticPart(i));}
    #[cfg(not(feature="detail-phases"))]
    let _=(obs,i);
}